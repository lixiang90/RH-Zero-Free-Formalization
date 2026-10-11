# Local zero-free shapes: scope and reproduction

The [paper](../papers/local-zero-free-shape-paper.pdf) and
[Lean module](../ZeroFree/LocalShape.lean) develop a local quartic shape using
the positive real part of the completed zeta logarithmic derivative.
The result is conditional on the global bound beta <= 7/8.

At sigma_c = 219/250 and T0 = 4000000000000, external Arb arithmetic certifies

```
14.49534467251349699 < Re(xi'/xi(sigma_c + i*T0))
                       < 14.49534467251349700 < 29/2.
```

For a hypothetical zero beta + i*gamma with beta > 1/2, its reflected zero
1-beta + i*gamma contributes another positive term. Put

```
a = sigma_c - beta, b = sigma_c + beta - 1,
c = 94/125, p = a*b, z = (gamma - T0)^2, E = 29/2,
S(p,z) = c*(p+z) - E*((p-z)^2 + c^2*z).
```

The region S > 0 in 1/2 < beta <= 7/8 excludes zeros. The exact rectangle
beta in [4/5,7/8], abs(gamma-T0) <= 1/200 is entirely inside that region.
Zeros to its right are excluded by the global bound, yielding sigma >= 4/5
throughout the closed height window. Conjugation gives the negative-height
copy. This does not improve the uniform strip for all heights.

The plot displays the actual quartic positive set and the assumed global
half-plane sigma > 7/8. At some heights these sets leave a gap; no such gap is filled
without a certificate. In the certified rectangle the sets connect.

## Verification layers

| Layer | Status |
|---|---|
| Rational constants, four corner values and positivity for every real rectangle point | Ordinary Lean kernel proofs |
| Pair identity and conditional quartic/rectangle/disk exclusions | Ordinary Lean kernel proofs with explicit premises |
| Global beta <= 7/8 | Imported analytic assumption, not reproved by LocalShape |
| Hadamard sum and reflection for actual zeta | Classical written analytic argument, not formalized by LocalShape |
| Actual K < 29/2 | External rigorous Arb enclosure, not a Lean-kernel certificate |
| Full actual-zeta shape theorem in Lean | Not claimed |

The finite weighted-anchor theorem provides a common exclusion certificate.
With nonnegative weights its pointwise exclusion set is contained in the
union of the single-anchor sets. A larger pointwise region needs additional
constraints, not just nonnegative weighting.

## Reproduction

Use the repository's pinned Lean/Mathlib environment:

```sh
lake update
lake exe cache get
lake build ZeroFree.LocalShape
python scripts/verify.py
```

The last command includes LocalShape in the full-library public-root audit.
The fresh module record is [local-shape-lean.json](../verification/local-shape-lean.json).
The [fresh integration record](../verification/local-shape-integration.json)
also reports successful compilation of all 19 library modules and a
transitive axiom audit of all 246 public theorems, with only the three
permitted foundational axioms. Its commands, source hashes, build log and
complete axiom log are retained alongside it.
The pre-existing 224-root Lean and Nano records are historical and do not
certify the new module. No new independent Nano replay is claimed.

External numeric reproduction, verified here with Python 3.12.5 and
python-flint 0.9.0:

```sh
python -m pip install python-flint==0.9.0
python scripts/local_shape_certificate.py
```

The script uses exact integer/rational inputs, computes zeta and its first
derivative together, includes the gamma and pole-removal terms in xi'/xi,
and repeats at 96 and 160 bits. It writes
[local-shape-arb.json](../verification/local-shape-arb.json), including the
script hash, versions, full enclosures and strict rational comparisons.
Use ordinary Python execution with assertions enabled, as in the command.

For the optional scientific plot:

```sh
python -m pip install matplotlib numpy
python scripts/local_shape_certificate.py --plot
```

This writes docs/local-shape-regions.png and docs/local-shape-regions.svg.
Floating plots illustrate the exact region; they are not proof inputs.

The paper is a standalone pdfLaTeX source. Build it separately without
overwriting the checked-in delivered PDF:

```sh
mkdir -p tmp/local-shape-paper
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/local-shape-paper papers/local-zero-free-shape-paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/local-shape-paper papers/local-zero-free-shape-paper.tex
```

The [paper manifest](../verification/local-shape-paper.json) records delivered
source/PDF hashes. This new work is maintained in RH-Zero-Free-Formalization
and is not synchronized to RH-Weil.
