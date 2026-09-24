"""Shared presentation layer for the experiment scripts.

Every figure uses the same small visual system: one validated colour palette,
hairline axes, a headline that says what to look at, and a footnote naming the
paper result and the status of the calculation.  Every script prints the same
short banner before its diagnostics and a closing reading after them.

Nothing in this module computes mathematics.  The calculations remain in the
experiment scripts, ``common.py`` and ``high_precision.py``.

The categorical colours are the first slots of a colour-vision-deficiency
checked palette, always assigned in the same order.  The diverging map has a
neutral grey midpoint, and the sequential map is a single hue.  Figures are
drawn on an opaque light surface so they stay legible in both GitHub themes.
"""

from __future__ import annotations

import textwrap
from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
from cycler import cycler
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.transforms import offset_copy

from common import FIGURE_DIR


# -----------------------------------------------------------------------------
# Colours
# -----------------------------------------------------------------------------

SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK_2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
WASH = "#f0efec"

# Categorical slots, in their fixed order.  Slots 1-3 separate under simulated
# protan/deutan vision for every pair; aqua is below 3:1 contrast on the
# surface, so any figure using it also labels its lines directly.
BLUE = "#2a78d6"
ORANGE = "#eb6834"
AQUA = "#1baf7a"
SERIES = (BLUE, ORANGE, AQUA)

# Single-hue sequential ramp (light = small) and a blue/red diverging map
# with a neutral midpoint.
SEQUENTIAL = LinearSegmentedColormap.from_list(
    "weil_sequential",
    ["#e8f1fd", "#b7d3f6", "#86b6ef", "#5598e7", "#2a78d6", "#1c5cab", "#104281", "#0d366b"],
)
DIVERGING = LinearSegmentedColormap.from_list(
    "weil_diverging",
    ["#0d366b", "#2a78d6", "#9ec5f4", WASH, "#f3b4ad", "#e34948", "#8c1c1c"],
)

# Status vocabulary shared with README.md.
IDENTITY = "numerical check of an exact finite identity"
THEOREM = "theorem visualization"
DIAGNOSTIC = "finite diagnostic"
EXPLORATORY = "exploratory moving experiment"


def use_style() -> None:
    """Apply the shared Matplotlib style."""

    mpl.rcParams.update(
        {
            "figure.facecolor": SURFACE,
            "figure.dpi": 100,
            "savefig.facecolor": SURFACE,
            "axes.facecolor": SURFACE,
            "axes.edgecolor": AXIS,
            "axes.linewidth": 0.8,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.grid": True,
            "axes.axisbelow": True,
            "axes.labelcolor": INK_2,
            "axes.labelsize": 9.5,
            "axes.titlesize": 9.5,
            "axes.titlecolor": INK,
            "axes.titlelocation": "left",
            "axes.titlepad": 6.0,
            "axes.prop_cycle": cycler(color=SERIES),
            "axes.formatter.use_mathtext": True,
            "axes.formatter.limits": (-3, 4),
            "grid.color": GRID,
            "grid.linewidth": 0.6,
            "grid.linestyle": "-",
            "xtick.color": AXIS,
            "ytick.color": AXIS,
            "xtick.labelcolor": INK_2,
            "ytick.labelcolor": INK_2,
            "xtick.labelsize": 8.5,
            "ytick.labelsize": 8.5,
            "xtick.major.size": 3.0,
            "ytick.major.size": 3.0,
            "lines.linewidth": 1.5,
            "lines.solid_capstyle": "round",
            "lines.solid_joinstyle": "round",
            "lines.markersize": 6.0,
            "lines.markeredgewidth": 0.0,
            "legend.frameon": False,
            "legend.fontsize": 8.5,
            "legend.labelcolor": INK_2,
            "legend.handlelength": 1.6,
            "font.family": "DejaVu Sans",
            "font.size": 9.5,
            "text.color": INK,
            "mathtext.fontset": "dejavusans",
            "image.cmap": "weil_sequential",
            # Reproducible SVG output: fixed element ids, glyphs as paths.
            "svg.hashsalt": "weil-form-operators",
            "svg.fonttype": "path",
        }
    )
    for cmap in (SEQUENTIAL, DIVERGING):
        if cmap.name not in mpl.colormaps:
            mpl.colormaps.register(cmap)


# -----------------------------------------------------------------------------
# Figure helpers
# -----------------------------------------------------------------------------


def sci(value: float, digits: int = 1) -> str:
    """Format a number as mathtext scientific notation, without the dollar signs."""

    if value == 0.0:
        return "0"
    mantissa, exponent = f"{value:.{digits}e}".split("e")
    exponent = int(exponent)
    if exponent == 0:
        return mantissa
    return rf"{mantissa}\times 10^{{{exponent}}}"


def marker_ring(**kwargs) -> dict:
    """Marker keywords for a filled dot with a surface-coloured ring."""

    return {"markeredgecolor": SURFACE, "markeredgewidth": 1.2, **kwargs}


def lollipop(ax, x, y, color: str, *, label: str | None = None, markersize: float = 5.5) -> None:
    """Thin stems from zero with ringed dots: one mark per discrete coefficient."""

    ax.vlines(x, 0.0, y, color=color, linewidth=1.3, zorder=2)
    ax.plot(x, y, linestyle="none", marker="o", markersize=markersize, color=color,
            label=label, zorder=3, **marker_ring())


def label_end(ax, x: float, y: float, text: str, *, dx: float = 5.0, dy: float = 0.0, **kwargs) -> None:
    """Direct label placed just beyond a data point, in ink rather than series colour."""

    ax.annotate(
        text,
        xy=(x, y),
        xytext=(dx, dy),
        textcoords="offset points",
        va="center",
        ha=kwargs.pop("ha", "left"),
        color=kwargs.pop("color", INK_2),
        fontsize=kwargs.pop("fontsize", 8.5),
        **kwargs,
    )


def note(ax, x: float, y: float, text: str, **kwargs) -> None:
    """A small muted annotation in data coordinates."""

    ax.text(
        x,
        y,
        text,
        color=kwargs.pop("color", INK_2),
        fontsize=kwargs.pop("fontsize", 8.5),
        **kwargs,
    )


def save(
    fig,
    filename: str,
    *,
    title: str,
    subtitle: str | None = None,
    source: str | None = None,
) -> Path:
    """Lay out, caption, and save one figure as a reproducible SVG.

    ``title`` states what the reader should see.  ``subtitle`` gives the
    formula or the measured numbers.  ``source`` names the paper result and
    the status of the calculation.  The captions sit outside the plotting
    canvas and are included by the tight bounding box.
    """

    fig.tight_layout(pad=0.6)
    renderer = fig.canvas.get_renderer()
    boxes = [ax.get_tightbbox(renderer) for ax in fig.axes if ax.get_visible()]
    inverse = fig.transFigure.inverted()
    left = min(inverse.transform((box.x0, box.y0))[0] for box in boxes)
    bottom = min(inverse.transform((box.x0, box.y0))[1] for box in boxes)
    left = max(left, 0.0)

    width_chars = int(fig.get_figwidth() * 13.5)
    top_offset = 6.0
    if subtitle:
        subtitle_text = fig.text(
            left,
            1.0,
            _wrap(subtitle, width_chars),
            transform=offset_copy(fig.transFigure, fig=fig, y=top_offset, units="points"),
            ha="left",
            va="bottom",
            color=INK_2,
            fontsize=9.0,
            linespacing=1.45,
        )
        height_px = subtitle_text.get_window_extent(renderer).height
        top_offset += height_px * 72.0 / fig.dpi + 5.0

    fig.text(
        left,
        1.0,
        _wrap(title, int(width_chars * 0.82)),
        transform=offset_copy(fig.transFigure, fig=fig, y=top_offset, units="points"),
        ha="left",
        va="bottom",
        color=INK,
        fontsize=12.0,
        fontweight="bold",
        linespacing=1.3,
    )

    if source:
        fig.text(
            left,
            bottom,
            _wrap(source, int(width_chars * 1.3)),
            transform=offset_copy(fig.transFigure, fig=fig, y=-8.0, units="points"),
            ha="left",
            va="top",
            color=MUTED,
            fontsize=7.8,
        )

    path = FIGURE_DIR / filename
    # dpi only affects artists a script marks as rasterized; the rest stays vector.
    fig.savefig(path, bbox_inches="tight", pad_inches=0.22, dpi=200, metadata={"Date": None})
    plt.close(fig)
    return path


def _wrap(text: str, width: int) -> str:
    """Wrap plain-text paragraphs; lines containing mathtext are left intact."""

    lines = []
    for paragraph in text.split("\n"):
        if "$" in paragraph or len(paragraph) <= width:
            lines.append(paragraph)
        else:
            lines.extend(textwrap.wrap(paragraph, width))
    return "\n".join(lines)


# -----------------------------------------------------------------------------
# Console helpers (ASCII only, so redirected output never hits an encoding error)
# -----------------------------------------------------------------------------

RULE_WIDTH = 78


def banner(number: int, title: str, *, status: str, reference: str, claim: str) -> None:
    """Print the opening block for one experiment."""

    print("=" * RULE_WIDTH)
    print(f"Experiment {number:02d} | {title}")
    print(f"{status.capitalize()} | {reference}")
    print("-" * RULE_WIDTH)
    _print_labelled("Claim", claim)
    print("-" * RULE_WIDTH)


def reading(text: str, *, figures: tuple[str, ...] = ()) -> None:
    """Print the closing interpretation and the figures written."""

    print("-" * RULE_WIDTH)
    _print_labelled("Reading", text)
    for i, name in enumerate(figures):
        label = "Figures" if i == 0 else ""
        print(f"{label:<9}figures/{name}")
    print()


def _print_labelled(label: str, text: str) -> None:
    lines = textwrap.wrap(text, RULE_WIDTH - 9)
    for i, line in enumerate(lines):
        print(f"{label if i == 0 else '':<9}{line}")
