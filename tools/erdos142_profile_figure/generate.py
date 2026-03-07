from __future__ import annotations

import math
from pathlib import Path
import sys

import numpy as np
from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.figure_utils import paste_latex

OUT = ROOT / "assets" / "erdos142" / "profile_matching_frontier.png"

WIDTH = 1600
HEIGHT = 900
BG = (249, 247, 240, 255)
PANEL = (255, 252, 245, 255)
INK = (32, 37, 41, 255)
MUTED = (90, 96, 103, 255)
GRID = (222, 215, 203, 255)
BLUE = (26, 91, 176, 255)
RED = (189, 69, 56, 255)
RED_SOFT = (215, 95, 79, 70)
RED_DARK = (164, 47, 36, 255)
GREEN = (38, 122, 77, 255)
GREEN_SOFT = (239, 247, 239, 255)
GREEN_BORDER = (191, 219, 191, 255)
GRAY_DASH = (122, 126, 133, 255)


def load_font(size: int, bold: bool = False) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    candidates = []
    if bold:
        candidates.extend(
            [
                "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
                "/usr/share/fonts/dejavu/DejaVuSans-Bold.ttf",
            ]
        )
    candidates.extend(
        [
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
            "/usr/share/fonts/dejavu/DejaVuSans.ttf",
        ]
    )
    for path in candidates:
        if Path(path).exists():
            return ImageFont.truetype(path, size=size)
    return ImageFont.load_default()


FONT_TITLE = load_font(34, bold=True)
FONT_SUBTITLE = load_font(24)
FONT_LABEL = load_font(22, bold=True)
FONT_TEXT = load_font(21)
FONT_SMALL = load_font(18)


def make_canvas() -> tuple[Image.Image, ImageDraw.ImageDraw]:
    image = Image.new("RGBA", (WIDTH, HEIGHT), BG)
    draw = ImageDraw.Draw(image)
    return image, draw


def draw_dashed_polyline(
    draw: ImageDraw.ImageDraw,
    points: list[tuple[int, int]],
    fill: tuple[int, int, int, int],
    width: int,
    dash: int = 9,
    gap: int = 7,
) -> None:
    for start in range(0, len(points) - 1, dash + gap):
        stop = min(start + dash, len(points))
        if stop - start >= 2:
            draw.line(points[start:stop], fill=fill, width=width)


def draw_dashed_vertical(
    draw: ImageDraw.ImageDraw,
    x: int,
    y0: int,
    y1: int,
    fill: tuple[int, int, int, int],
    width: int,
    dash: int = 10,
    gap: int = 8,
) -> None:
    y = y0
    while y < y1:
        y_end = min(y + dash, y1)
        draw.line((x, y, x, y_end), fill=fill, width=width)
        y += dash + gap


def draw_dashed_horizontal(
    draw: ImageDraw.ImageDraw,
    x0: int,
    x1: int,
    y: int,
    fill: tuple[int, int, int, int],
    width: int,
    dash: int = 9,
    gap: int = 7,
) -> None:
    x = x0
    while x < x1:
        x_end = min(x + dash, x1)
        draw.line((x, y, x_end, y), fill=fill, width=width)
        x += dash + gap


def wrap_text(
    draw: ImageDraw.ImageDraw,
    text: str,
    font: ImageFont.FreeTypeFont | ImageFont.ImageFont,
    max_width: int,
) -> str:
    lines: list[str] = []
    for paragraph in text.split("\n"):
        words = paragraph.split()
        if not words:
            lines.append("")
            continue
        current = words[0]
        for word in words[1:]:
            candidate = f"{current} {word}"
            if draw.textbbox((0, 0), candidate, font=font)[2] <= max_width:
                current = candidate
            else:
                lines.append(current)
                current = word
        lines.append(current)
    return "\n".join(lines)


def draw_panel(
    image: Image.Image,
    draw: ImageDraw.ImageDraw,
    box: tuple[int, int, int, int],
    title_tex: str,
    upper_fn,
    lower_fn,
    envelope_factor: float,
    upper_label_tex: str,
    lower_label_tex: str,
    envelope_label_tex: str,
    missing_formula_tex: str,
    target_formula_tex: str,
    target_suffix_tex: str | None = None,
) -> None:
    x0, y0, x1, y1 = box
    draw.rounded_rectangle(box, radius=24, fill=PANEL, outline=GRID, width=2)

    paste_latex(image, (x0 + 26, y0 + 18), title_tex, color=INK, density=260)
    paste_latex(
        image,
        (x0 + 26, y0 + 54),
        r"{\sffamily schematic decay profiles; common factor $N$ suppressed}",
        color=MUTED,
        density=180,
    )

    plot_left = x0 + 62
    plot_right = x1 - 44
    plot_top = y0 + 120
    plot_bottom = y1 - 154

    draw.line((plot_left, plot_bottom, plot_right, plot_bottom), fill=INK, width=2)
    draw.line((plot_left, plot_bottom, plot_left, plot_top), fill=INK, width=2)

    for frac in (0.25, 0.5, 0.75):
        y = plot_bottom - frac * (plot_bottom - plot_top)
        draw.line((plot_left, y, plot_right, y), fill=GRID, width=1)
    for frac in (0.25, 0.5, 0.75):
        x = plot_left + frac * (plot_right - plot_left)
        draw.line((x, plot_top, x, plot_bottom), fill=GRID, width=1)

    paste_latex(
        image,
        (plot_right - 108, plot_bottom + 12),
        r"{\sffamily larger $N$}",
        color=MUTED,
        density=180,
    )
    draw.text((plot_left - 12, plot_top - 30), "profile size", fill=MUTED, font=FONT_SMALL)

    samples = np.exp(np.linspace(math.log(16.0), math.log(1e8), 360))
    upper_vals = np.array([upper_fn(v) for v in samples], dtype=float)
    lower_vals = np.array([lower_fn(v) for v in samples], dtype=float)
    envelope_vals = envelope_factor * lower_vals

    ymin = min(upper_vals.min(), lower_vals.min(), envelope_vals.min())
    ymax = max(upper_vals.max(), lower_vals.max(), envelope_vals.max())
    ypad = 0.08 * (ymax - ymin)
    ymin -= ypad
    ymax += ypad

    def map_x(i: int) -> int:
        return int(plot_left + i * (plot_right - plot_left) / (len(samples) - 1))

    def map_y(v: float) -> int:
        t = (v - ymin) / (ymax - ymin)
        return int(plot_bottom - t * (plot_bottom - plot_top))

    upper_points = [(map_x(i), map_y(v)) for i, v in enumerate(upper_vals)]
    lower_points = [(map_x(i), map_y(v)) for i, v in enumerate(lower_vals)]
    envelope_points = [(map_x(i), map_y(v)) for i, v in enumerate(envelope_vals)]
    bad_mask = upper_vals > envelope_vals

    start = None
    for i, bad in enumerate(bad_mask):
        if bad and start is None:
            start = i
        if start is not None and (i == len(bad_mask) - 1 or not bad_mask[i + 1]):
            stop = i
            polygon = upper_points[start : stop + 1] + list(reversed(envelope_points[start : stop + 1]))
            if len(polygon) >= 3:
                draw.polygon(polygon, fill=RED_SOFT)
            start = None

    if np.any(bad_mask):
        threshold_index = min(np.max(np.nonzero(bad_mask)[0]) + 1, len(samples) - 1)
        threshold_x = envelope_points[threshold_index][0]
        draw_dashed_vertical(draw, threshold_x, plot_top, plot_bottom, fill=GRAY_DASH, width=2)
        paste_latex(image, (threshold_x + 10, plot_top + 6), r"$N_0$", color=GRAY_DASH, density=180)

    draw.line(lower_points, fill=RED, width=5)
    draw_dashed_polyline(draw, envelope_points, fill=RED_DARK, width=3)
    draw.line(upper_points, fill=BLUE, width=5)

    legend_y = y0 + 84
    legend_x0 = x1 - 350
    draw.line((legend_x0, legend_y, legend_x0 + 40, legend_y), fill=BLUE, width=5)
    paste_latex(image, (legend_x0 + 52, legend_y - 12), upper_label_tex, color=INK, density=180)
    draw.line((legend_x0, legend_y + 28, legend_x0 + 40, legend_y + 28), fill=RED, width=5)
    paste_latex(image, (legend_x0 + 52, legend_y + 16), lower_label_tex, color=INK, density=180)
    draw_dashed_horizontal(draw, legend_x0, legend_x0 + 40, legend_y + 56, fill=RED_DARK, width=3, dash=7, gap=5)
    paste_latex(image, (legend_x0 + 52, legend_y + 44), envelope_label_tex, color=INK, density=180)

    if np.any(bad_mask):
        bad_indices = np.nonzero(bad_mask)[0]
        anchor = bad_indices[min(len(bad_indices) // 2, len(bad_indices) - 1)]
        label_pos = (
            min(upper_points[anchor][0] + 36, plot_right - 220),
            max(plot_top + 28, upper_points[anchor][1] - 64),
        )
        paste_latex(image, label_pos, r"{\sffamily\bfseries missing region:}", color=RED_DARK, density=190)
        paste_latex(image, (label_pos[0], label_pos[1] + 24), missing_formula_tex, color=RED_DARK, density=190)

    target_box = (x0 + 26, y1 - 116, x1 - 26, y1 - 26)
    draw.rounded_rectangle(target_box, radius=18, fill=GREEN_SOFT, outline=GREEN_BORDER, width=2)
    paste_latex(
        image,
        (target_box[0] + 18, target_box[1] + 12),
        r"{\sffamily prove eventual domination:}",
        color=GREEN,
        density=190,
    )
    paste_latex(
        image,
        (target_box[0] + 18, target_box[1] + 36),
        target_formula_tex,
        color=GREEN,
        density=190,
    )
    if target_suffix_tex is not None:
        paste_latex(
            image,
            (target_box[0] + 18, target_box[1] + 59),
            target_suffix_tex,
            color=GREEN,
            density=190,
        )


def main() -> None:
    image, draw = make_canvas()

    draw.text((54, 36), "Erdos #142 profile-matching frontier", fill=INK, font=FONT_TITLE)
    subtitle = wrap_text(
        draw,
        "The higher-branch gap is to show that the current upper template is eventually bounded by a constant multiple of the current lower template.",
        FONT_SUBTITLE,
        WIDTH - 110,
    )
    draw.multiline_text((54, 82), subtitle, fill=MUTED, font=FONT_SUBTITLE, spacing=6)

    left_panel = (48, 150, WIDTH // 2 - 20, HEIGHT - 60)
    right_panel = (WIDTH // 2 + 20, 150, WIDTH - 48, HEIGHT - 60)

    draw_panel(
        image,
        draw,
        left_panel,
        r"{\sffamily\bfseries (1) $k = 4$ branch}",
        upper_fn=lambda n: 1.35 / (math.log(n + 2.0) ** 1.20),
        lower_fn=lambda n: 0.82 / (math.log(n + 2.0) ** 0.92),
        envelope_factor=1.18,
        upper_label_tex=r"$U_4(N)/N$",
        lower_label_tex=r"$L_4(N)/N$",
        envelope_label_tex=r"$A L_4(N)/N$",
        missing_formula_tex=r"$U_4(N) > A L_4(N)$",
        target_formula_tex=r"$U_4(N)=O(L_4(N))$",
    )

    draw_panel(
        image,
        draw,
        right_panel,
        r"{\sffamily\bfseries (2) fixed $k \ge 5$ branch}",
        upper_fn=lambda n: 1.25 / (math.log(math.log(n + 3.0)) ** 1.55),
        lower_fn=lambda n: 0.86 / (math.log(math.log(n + 3.0)) ** 0.98),
        envelope_factor=1.18,
        upper_label_tex=r"$U_k(N)/N$",
        lower_label_tex=r"$L_k(N)/N$",
        envelope_label_tex=r"$A L_k(N)/N$",
        missing_formula_tex=r"$U_k(N) > A L_k(N)$",
        target_formula_tex=r"$U_k(N)=O(L_k(N))$",
        target_suffix_tex=r"{\sffamily for fixed $k \ge 5$}",
    )

    footer = (
        "Schematic only. The plot shows the decay profiles after suppressing the common factor N and the harmless shifts inside the logarithms."
    )
    wrapped_footer = wrap_text(draw, footer, FONT_SMALL, WIDTH - 110)
    draw.multiline_text((54, HEIGHT - 56), wrapped_footer, fill=MUTED, font=FONT_SMALL, spacing=4)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    image.save(OUT, format="PNG", optimize=True)


if __name__ == "__main__":
    main()
