from __future__ import annotations

import math
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "assets" / "erdos142" / "profile_matching_frontier.png"

WIDTH = 1600
HEIGHT = 900
BG = (249, 247, 240)
PANEL = (255, 252, 245)
INK = (32, 37, 41)
MUTED = (90, 96, 103)
GRID = (222, 215, 203)
BLUE = (26, 91, 176)
RED = (189, 69, 56)
GREEN = (38, 122, 77)


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
    image = Image.new("RGB", (WIDTH, HEIGHT), BG)
    draw = ImageDraw.Draw(image)
    return image, draw


def draw_panel(
    draw: ImageDraw.ImageDraw,
    box: tuple[int, int, int, int],
    title: str,
    upper_fn,
    lower_fn,
    upper_label: str,
    lower_label: str,
    target_label: str,
) -> None:
    x0, y0, x1, y1 = box
    draw.rounded_rectangle(box, radius=24, fill=PANEL, outline=GRID, width=2)

    draw.text((x0 + 26, y0 + 20), title, fill=INK, font=FONT_LABEL)
    draw.text(
        (x0 + 26, y0 + 54),
        "schematic decay profiles; common factor N suppressed",
        fill=MUTED,
        font=FONT_SMALL,
    )

    plot_left = x0 + 62
    plot_right = x1 - 44
    plot_top = y0 + 120
    plot_bottom = y1 - 128

    draw.line((plot_left, plot_bottom, plot_right, plot_bottom), fill=INK, width=2)
    draw.line((plot_left, plot_bottom, plot_left, plot_top), fill=INK, width=2)

    for frac in (0.25, 0.5, 0.75):
        y = plot_bottom - frac * (plot_bottom - plot_top)
        draw.line((plot_left, y, plot_right, y), fill=GRID, width=1)
    for frac in (0.25, 0.5, 0.75):
        x = plot_left + frac * (plot_right - plot_left)
        draw.line((x, plot_top, x, plot_bottom), fill=GRID, width=1)

    draw.text((plot_right - 90, plot_bottom + 14), "larger N", fill=MUTED, font=FONT_SMALL)
    draw.text((plot_left - 12, plot_top - 30), "profile size", fill=MUTED, font=FONT_SMALL)

    samples = np.exp(np.linspace(math.log(16.0), math.log(1e8), 360))
    upper_vals = np.array([upper_fn(v) for v in samples], dtype=float)
    lower_vals = np.array([lower_fn(v) for v in samples], dtype=float)

    ymin = min(upper_vals.min(), lower_vals.min())
    ymax = max(upper_vals.max(), lower_vals.max())
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

    draw.line(lower_points, fill=RED, width=5)
    draw.line(upper_points, fill=BLUE, width=5)

    legend_y = y0 + 84
    draw.line((x1 - 360, legend_y, x1 - 320, legend_y), fill=BLUE, width=5)
    draw.text((x1 - 310, legend_y - 11), upper_label, fill=INK, font=FONT_SMALL)
    draw.line((x1 - 360, legend_y + 28, x1 - 320, legend_y + 28), fill=RED, width=5)
    draw.text((x1 - 310, legend_y + 17), lower_label, fill=INK, font=FONT_SMALL)

    target_box = (x0 + 26, y1 - 88, x1 - 26, y1 - 26)
    draw.rounded_rectangle(target_box, radius=18, fill=(239, 247, 239), outline=(191, 219, 191), width=2)
    draw.text((target_box[0] + 18, target_box[1] + 14), target_label, fill=GREEN, font=FONT_TEXT)


def main() -> None:
    image, draw = make_canvas()

    draw.text((54, 36), "Erdos #142 profile-matching frontier", fill=INK, font=FONT_TITLE)
    draw.text(
        (54, 82),
        "The higher-branch gap is to show that the current upper template is eventually bounded by a constant multiple of the current lower template.",
        fill=MUTED,
        font=FONT_SUBTITLE,
    )

    left_panel = (48, 150, WIDTH // 2 - 20, HEIGHT - 60)
    right_panel = (WIDTH // 2 + 20, 150, WIDTH - 48, HEIGHT - 60)

    draw_panel(
        draw,
        left_panel,
        "k = 4 polylog branch",
        upper_fn=lambda n: 1.0 / (math.log(n + 2.0) ** 1.55),
        lower_fn=lambda n: 0.82 / (math.log(n + 2.0) ** 0.92),
        upper_label="split upper template U4",
        lower_label="split lower template L4",
        target_label="Missing theorem: U4(N) = O(L4(N)) as N -> infinity",
    )

    draw_panel(
        draw,
        right_panel,
        "k >= 5 iterated-log branch",
        upper_fn=lambda n: 1.0 / (math.log(math.log(n + 3.0)) ** 1.60),
        lower_fn=lambda n: 0.86 / (math.log(math.log(n + 3.0)) ** 0.98),
        upper_label="split upper template Uk",
        lower_label="split lower template Lk",
        target_label="Missing theorem: Uk(N) = O(Lk(N)) for each fixed k >= 5",
    )

    footer = (
        "Schematic only. The plot shows the decay profiles after suppressing the common factor N and the harmless shifts inside the logarithms."
    )
    draw.text((54, HEIGHT - 38), footer, fill=MUTED, font=FONT_SMALL)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    image.save(OUT, format="PNG", optimize=True)


if __name__ == "__main__":
    main()
