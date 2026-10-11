# Zero-free-region papers

Author of the new local shape paper and formalization: Li Xiang / lixiang90.
The three older archived copies preserve their original delivered bytes
and metadata.

| Paper | Source | PDF | Boundary |
|---|---|---|---|
| Local reflected-pair shapes | [TeX](local-zero-free-shape-paper.tex) | [PDF](local-zero-free-shape-paper.pdf) | Conditional quartic shape; sigma >= 4/5 and abs(t - 4e12) <= 1/200 |
| Cubic feedback, current best | [TeX](kappa-feedback-cubic-boundary-paper.tex) | [PDF](kappa-feedback-cubic-boundary-paper.pdf) | sigmaStar = 0.874957019420098946... |
| Free-b predecessor | [TeX](free-b-compensated-probe-boundary-paper.tex) | [PDF](free-b-compensated-probe-boundary-paper.pdf) | (1507 - 2 sqrt(921))/1653 |
| Rational predecessor | [TeX](seven-eighths-boundary-improvement-paper.tex) | [PDF](seven-eighths-boundary-improvement-paper.pdf) | 69999/80000 |

The local shape result assumes the global seven-eighths zero bound and uses
an external Arb certificate. Its finite algebra and conditional exclusions
are kernel checked; its complete analytic/numeric specialization is not
an end-to-end Lean theorem. The three older papers remain relative to their
imported analytic package. New code does not retroactively promote them to
unconditional Lean proofs.
Current status: [proof-status.md](../docs/proof-status.md).

The [historical provenance manifest](../verification/paper-provenance.json)
binds the three older TeX/PDF pairs to their RH-Weil source commit. The new
paper is authored and maintained here, with its own
[manifest](../verification/local-shape-paper.json), and is not synchronized
to RH-Weil. All four papers are standalone pdfLaTeX documents.
Rebuild without overwriting a delivered PDF:

```sh
mkdir -p tmp/paper-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/paper-build papers/kappa-feedback-cubic-boundary-paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/paper-build papers/kappa-feedback-cubic-boundary-paper.tex
```
