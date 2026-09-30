# Paper and arXiv source

This directory contains the source for the Pascal Minus-One GCD research paper,
now public on arXiv as [arXiv:2609.37754](https://arxiv.org/abs/2609.37754)
(`math.NT`). Version 1 was submitted on 29 September 2026 under the title
*Restricted Binomial GCDs at Primes Congruent to -1*.

- `main.tex`: single-file LaTeX source for the paper.
- `pascal-minus-one-paper.pdf`: locally compiled repository copy of the paper.
- `PREFLIGHT.md`: arXiv technical and policy pre-flight record, retained as an audit trail.
- `LEAN_ALIGNMENT.md`: theorem-to-Lean statement alignment note.

The clean arXiv upload zip is generated from `main.tex` and is intentionally not
committed as repository source. The canonical public preprint record is the arXiv
entry linked above; the generated upload bundle is not required for the Lean theorem
layer.
