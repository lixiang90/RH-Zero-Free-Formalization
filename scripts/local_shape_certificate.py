"""Reproduce a local zero-free shape certificate, conditional on beta <= 7/8.

The FLINT/Arb enclosure is rigorous external arithmetic, not a Lean proof.
The analytic input is the Hadamard real-part identity for completed xi,
with every zero term positive to the right of the assumed global boundary.
Run: python scripts/local_shape_certificate.py --plot
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import platform
from time import perf_counter

import flint
from flint import acb, acb_series, arb, ctx

HEIGHT = 4_000_000_000_000
ANCHOR = Q(219, 250)
BASELINE = Q(7, 8)
UPPER = Q(29, 2)
C = 2 * ANCHOR - 1
SIGMA_MIN = Q(4, 5)
HALF_HEIGHT = Q(1, 200)
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
DOCS = ROOT / "docs"


def aq(q: Q) -> arb:
    return arb(q.numerator) / q.denominator


def rational(q: Q) -> str:
    return f"{q.numerator}/{q.denominator}"


def evaluate(bits: int) -> dict:
    ctx.prec = bits
    ctx.cap = 2
    start = perf_counter()
    s = acb(aq(ANCHOR), HEIGHT)
    jet = acb_series([s, 1], 2).zeta()
    assert not jet[0].contains(0), "zeta value enclosure contains zero"
    k = (
        1 / s
        + 1 / (s - 1)
        - arb.pi().log() / 2
        + (s / 2).digamma() / 2
        + jet[1] / jet[0]
    ).real
    lower = Q(1449534467251349699, 10**17)
    upper = Q(1449534467251349700, 10**17)
    assert k.is_finite()
    assert aq(lower) < k < aq(upper)
    assert k < aq(UPPER)
    return {
        "precision_bits": bits,
        "elapsed_seconds": perf_counter() - start,
        "zeta_enclosure": str(jet[0]),
        "zeta_prime_enclosure": str(jet[1]),
        "xi_log_derivative_real_enclosure": str(k),
        "rational_lower": rational(lower),
        "rational_upper": rational(upper),
        "strict_upper_E": rational(UPPER),
        "all_enclosure_comparisons_passed": True,
    }


def exact_geometry() -> dict:
    a_lo = ANCHOR - BASELINE
    a_hi = ANCHOR - SIGMA_MIN
    assert 0 < a_lo < a_hi < C / 2
    p_lo = a_lo * (C - a_lo)
    p_hi = a_hi * (C - a_hi)
    z_hi = HALF_HEIGHT**2
    assert p_lo == Q(751, 10**6)
    assert p_hi == Q(3211, 62500)
    assert z_hi == Q(1, 40000)
    corners = []
    for p in (p_lo, p_hi):
        for z in (Q(0), z_hi):
            value = C * (p + z) - UPPER * ((p - z)**2 + C**2 * z)
            assert value > 0
            corners.append({"p": rational(p), "z": rational(z), "S": rational(value)})
    # S is jointly concave: its quadratic part is -E*(p-z)^2.
    # Every rectangle point is a convex combination of its four corners.
    # Therefore S >= min(corner values) > 0 throughout the rectangle.
    radius = 1 / (2 * UPPER)
    center = ANCHOR - radius
    return {
        "pair_kernel_identity": "K_pair = c*(p+z) / ((p-z)^2+c^2*z)",
        "polynomial": "S=c*(p+z)-E*((p-z)^2+c^2*z)",
        "concavity": "Hessian = -2E * [[1,-1],[-1,1]]; E>0",
        "p_interval": [rational(p_lo), rational(p_hi)],
        "z_interval": ["0/1", rational(z_hi)],
        "positive_corner_values": corners,
        "minimum_corner": rational(min(Q(row["S"]) for row in corners)),
        "single_zero_disk": {"real_center": rational(center), "radius": rational(radius)},
        "conditional_rectangle": {
            "real_part_at_least": rational(SIGMA_MIN),
            "imaginary_center": HEIGHT,
            "imaginary_half_width": rational(HALF_HEIGHT),
            "negative_height_copy": "by conjugation",
        },
    }


def plot_regions() -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Patch, Rectangle
    import numpy as np

    boundary = float(BASELINE)
    xs = np.linspace(.79, .887, 1401)
    us = np.linspace(-.045, .045, 1101)
    xx, uu = np.meshgrid(xs, us)
    a = float(ANCHOR) - xx
    b = float(ANCHOR) + xx - 1
    pair = a / (a*a + uu*uu) + b / (b*b + uu*uu)
    old = xx > boundary
    added = (xx <= boundary) & (xx > .5) & (pair > float(UPPER))
    r = float(1 / (2 * UPPER))
    circle_x = float(ANCHOR) - r
    fig, ax = plt.subplots(figsize=(10, 7.2), constrained_layout=True)
    ax.contourf(xx, uu, old.astype(int), levels=[.5, 1.5], colors=["#cbdcf1"])
    ax.contourf(xx, uu, added.astype(int), levels=[.5, 1.5], colors=["#91d1bd"])
    ax.contour(xx, uu, pair, levels=[float(UPPER)], colors=["#08785c"], linewidths=1.5)
    theta = np.linspace(0, 2*np.pi, 1000)
    ax.plot(circle_x + r*np.cos(theta), r*np.sin(theta), "--", color="#d08c1b", linewidth=1.3)
    ax.axvline(boundary, color="#345e95", linewidth=1.5)
    ax.add_patch(Rectangle((float(SIGMA_MIN), -float(HALF_HEIGHT)),
                           boundary-float(SIGMA_MIN), 2*float(HALF_HEIGHT),
                           fill=False, edgecolor="#9e2942", linewidth=1.8))
    ax.plot([float(ANCHOR)], [0], "ko", markersize=4)
    ax.annotate("anchor: 0.876 + iT0", (float(ANCHOR), 0),
                xytext=(.85, .041), fontsize=10,
                arrowprops={"arrowstyle": "->", "color": "black"})
    ax.set(xlim=(.79, .887), ylim=(-.045, .045),
           xlabel="Real part sigma", ylabel="Imaginary offset t - T0",
           title="Local zero-free extension at T0 = 4 x 10^12\n"
                 "Conditional on the global strip; external Arb certificate K < 14.5")
    ax.grid(alpha=.18)
    ax.legend(handles=[Patch(color="#cbdcf1", label="Assumed global half-plane sigma > 7/8"),
                       Patch(color="#91d1bd", label="Added reflected-pair kernel region"),
                       plt.Line2D([], [], color="#d08c1b", linestyle="--", label="Single-zero disk"),
                       plt.Line2D([], [], color="#9e2942", label="Exact rectangle: sigma >= 0.8, |t-T0| <= 0.005")],
              loc="lower left", fontsize=9)
    DOCS.mkdir(exist_ok=True)
    fig.savefig(DOCS / "local-shape-regions.png", dpi=180)
    fig.savefig(DOCS / "local-shape-regions.svg")
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plot", action="store_true")
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    data = {
        "scope": "Conditional local zero-free certificate, not an unconditional Lean theorem",
        "assumptions": [
            "All nontrivial zeta zeros satisfy beta <= 7/8",
            "Classical Hadamard real-part identity for xi with multiplicities",
            "Functional-equation reflection rho -> 1-conjugate(rho)",
        ],
        "formalization_status": {
            "Arb_enclosures": "externally verified; not Lean-kernel certified",
            "global_strip": "input; not reproved here",
            "Hadamard_identity": "classical analytic input; not formalized by this script",
            "geometry": "real rectangle positivity and quartic conditional exclusion kernel-checked in ZeroFree/LocalShape.lean",
            "Lean_analytic_scope": "generic zero predicate; global strip, pair-kernel majorization and numerical upper bound remain explicit inputs",
        },
        "environment": {
            "python": platform.python_version(),
            "python_flint": flint.__version__,
            "linked_flint": getattr(flint, "__FLINT_VERSION__", "unavailable"),
        },
        "exact_anchor": {"real": rational(ANCHOR), "imaginary": HEIGHT},
        "replays": [evaluate(96), evaluate(160)],
        "geometry": exact_geometry(),
    }
    data["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (OUT / "local-shape-arb.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    if args.plot:
        plot_regions()
    print(json.dumps({"K": data["replays"][-1]["xi_log_derivative_real_enclosure"],
                      "E": rational(UPPER),
                      "rectangle": data["geometry"]["conditional_rectangle"],
                      "minimum_corner_S": data["geometry"]["minimum_corner"],
                      "output": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
