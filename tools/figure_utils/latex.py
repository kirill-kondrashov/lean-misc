from __future__ import annotations

from functools import lru_cache
import hashlib
from pathlib import Path
import subprocess
import tempfile

from PIL import Image


DEFAULT_PACKAGES: tuple[str, ...] = ("amsmath", "amssymb")


def _build_document(source: str, border: int, packages: tuple[str, ...]) -> str:
    package_lines = "\n".join(f"\\usepackage{{{package}}}" for package in packages)
    return rf"""\documentclass[preview,border={border}pt]{{standalone}}
{package_lines}
\begin{{document}}
{source}
\end{{document}}
"""


@lru_cache(maxsize=None)
def render_latex_mask(
    source: str,
    density: int = 220,
    border: int = 2,
    packages: tuple[str, ...] = DEFAULT_PACKAGES,
) -> Image.Image:
    doc = _build_document(source, border=border, packages=packages)
    key = hashlib.sha256(f"{density}:{border}:{packages}:{source}".encode("utf-8")).hexdigest()[:16]
    with tempfile.TemporaryDirectory(prefix=f"figure-tex-{key}-") as tmp:
        tmp_path = Path(tmp)
        tex_path = tmp_path / "snippet.tex"
        dvi_path = tmp_path / "snippet.dvi"
        png_path = tmp_path / "snippet.png"
        tex_path.write_text(doc, encoding="utf-8")
        latex = subprocess.run(
            ["latex", "-interaction=nonstopmode", "-halt-on-error", tex_path.name],
            cwd=tmp_path,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        if latex.returncode != 0:
            raise RuntimeError(f"LaTeX rendering failed for {source!r}:\n{latex.stdout}")
        dvipng = subprocess.run(
            ["dvipng", "-D", str(density), "-T", "tight", "-bg", "Transparent", "-o", png_path.name, dvi_path.name],
            cwd=tmp_path,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        if dvipng.returncode != 0:
            raise RuntimeError(f"dvipng rendering failed for {source!r}:\n{dvipng.stdout}")
        rendered = Image.open(png_path).convert("RGBA")
        mask = Image.new("RGBA", rendered.size, (255, 255, 255, 0))
        mask.putalpha(rendered.getchannel("A"))
        return mask.copy()


def colorize_latex(mask: Image.Image, color: tuple[int, int, int, int]) -> Image.Image:
    colored = Image.new("RGBA", mask.size, color)
    colored.putalpha(mask.getchannel("A"))
    return colored


def paste_latex(
    image: Image.Image,
    position: tuple[int, int],
    source: str,
    color: tuple[int, int, int, int],
    density: int = 220,
    border: int = 2,
    packages: tuple[str, ...] = DEFAULT_PACKAGES,
) -> tuple[int, int]:
    mask = render_latex_mask(source, density=density, border=border, packages=packages)
    colored = colorize_latex(mask, color)
    image.alpha_composite(colored, position)
    return colored.size
