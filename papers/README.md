# Archived zero-free-region papers

Author of the new formalization: Li Xiang / lixiang90. Copies preserve
the original delivered bytes and metadata.

| Paper | Source | PDF | Boundary |
|---|---|---|---|
| Cubic feedback, current best | [TeX](kappa-feedback-cubic-boundary-paper.tex) | [PDF](kappa-feedback-cubic-boundary-paper.pdf) | sigmaStar = 0.874957019420098946... |
| Free-b predecessor | [TeX](free-b-compensated-probe-boundary-paper.tex) | [PDF](free-b-compensated-probe-boundary-paper.pdf) | (1507 - 2 sqrt(921))/1653 |
| Rational predecessor | [TeX](seven-eighths-boundary-improvement-paper.tex) | [PDF](seven-eighths-boundary-improvement-paper.pdf) | 69999/80000 |

All conclusions are relative to their imported analytic package. New code
does not retroactively promote them to unconditional Lean proofs.
Current status: [proof-status.md](../docs/proof-status.md).

The [provenance manifest](../verification/paper-provenance.json) binds every
TeX/PDF byte to its RH-Weil source commit. They are standalone pdfLaTeX documents.
Rebuild without overwriting a delivered PDF:

```sh
mkdir -p tmp/paper-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/paper-build papers/kappa-feedback-cubic-boundary-paper.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/paper-build papers/kappa-feedback-cubic-boundary-paper.tex
```
