"""Small precision helpers shared by the demonstration scripts.

The default experiments use NumPy float64 because it is fast, familiar, and
ideal for visualization.  A few experiments can optionally repeat their core
calculation with mpmath at higher precision.

The precision ladder is intentionally modest:

    float64  -> ordinary NumPy calculations and plots
    mp50     -> 50 decimal digits
    mp100    -> 100 decimal digits
    mp200    -> 200 decimal digits

A custom digit count can be supplied with ``--dps``.  The high-precision path
is for understanding numerical stability, not for proof-grade certification.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass


PROFILES = {
    "float64": None,
    "mp50": 50,
    "mp100": 100,
    "mp200": 200,
}


@dataclass(frozen=True)
class PrecisionChoice:
    """Resolved precision choice for one experiment."""

    name: str
    dps: int | None

    @property
    def uses_mpmath(self) -> bool:
        return self.dps is not None


def add_precision_arguments(parser: argparse.ArgumentParser) -> None:
    """Add the same simple precision options to an experiment parser."""

    parser.add_argument(
        "--precision",
        choices=tuple(PROFILES),
        default="float64",
        help="numerical backend/profile (default: float64)",
    )
    parser.add_argument(
        "--dps",
        type=int,
        default=None,
        help="custom mpmath decimal digits; overrides --precision",
    )


def resolve_precision(args: argparse.Namespace) -> PrecisionChoice:
    """Resolve ``--precision`` and optional ``--dps`` into one choice."""

    if args.dps is not None:
        if args.dps < 20:
            raise ValueError("--dps should be at least 20 for these demos")
        return PrecisionChoice(name=f"mp{args.dps}", dps=args.dps)

    return PrecisionChoice(name=args.precision, dps=PROFILES[args.precision])


def configure_mpmath(dps: int):
    """Import mpmath lazily and set its working precision."""

    try:
        import mpmath as mp
    except ImportError as exc:  # pragma: no cover - friendly public-repo error
        raise RuntimeError(
            "High-precision mode needs mpmath. Install it with "
            "`python -m pip install mpmath`."
        ) from exc

    mp.mp.dps = dps
    return mp
