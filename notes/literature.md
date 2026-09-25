# Literature boundary

A source-level literature audit was completed on **25 September 2026**. The detailed
comparison, bibliography and contribution map are in
[the September 2026 novelty audit](novelty-audit-2026-09.md).

## Current conclusion

The audit located **no mathematically equivalent prior theorem for the full
`p ≡ -1 (mod m)` valuation formula** formalised in this repository.

The supported public wording is:

> A source-level literature audit through September 2026 located no equivalent prior
> theorem for the full `p ≡ -1 (mod m)` valuation formula. McTague's 2017 theorem and
> its same-residue weakening cover the `p ≡ 1 (mod m)` branch and part of the
> minus-one `p>m` regime, but not the mixed-parity branch or the general `p=m-1`
> classification proved here.

This is an apparent-extension claim, not an unconditional priority claim. The
repository does not presently use wording such as "first" or "new theorem".

## McTague boundary

Carl McTague's Theorem Q studies exactly the same restricted gcd family, after the
renaming `n=N` and `q=m`:

[
gcd_{0<k<n/q}inom n{qk}.
]

For `p ≡ 1 (mod q)` it gives the exact `p`-adic valuation in terms of the base-`p`
digit sum. In the regime `q|n`, this is mathematically the plus-one branch formalised
here, so that branch is not claimed as a new mathematical result.

The corrected first remark on page 2 of arXiv:1510.06696v5 also weakens
`p ≡ 1 (mod q)` to a same-residue condition on the powers of `p` occurring in a
minimal power-sum expansion, with a size condition `p>q`.

For `p ≡ -1 (mod m)`, the residues of `p^i` are `(-1)^i mod m`. Hence this
same-residue weakening covers the repository's one-parity cases

[
(A,B)=(m,0)quad	ext{and}quad(0,m)
]

when `p>m`. It does **not** cover the mixed case `(A,B)=(1,1)`, and its `p>m`
hypothesis excludes the low-prime case `p=m-1`.

McTague also explicitly records

[
v_2!left(gcd_{0<k<2}inom6{3k}ight)=2,
]

which is the `m=3`, `p=2=m-1`, `N=6` instance of the exceptional valuation-2
phenomenon. The existence of such an exception is therefore known; the audit located
no prior **general** theorem giving the repository's `p=m-1`, `(A,B)=(1,1)`
classification.

Primary source:

- Carl McTague, *On the Greatest Common Divisor of Binomial Coefficients
  C(n,q), C(n,2q), C(n,3q), ...*, American Mathematical Monthly 124(4) (2017),
  353–356, DOI 10.4169/amer.math.monthly.124.4.353,
  https://arxiv.org/abs/1510.06696.

## Wu 2026

Chai Wah Wu's 2026 preprint studies

[
g(m,n)=gcd_{1le k<n}inom{mn}{mk},
]

so it is the same gcd object under `N=mn`. Its computable formulas impose hypotheses
including prime-power moduli and relevant non-modulus primes congruent to
`1 (mod m)`. Those hypotheses do not settle the general minus-one theorem formalised
here.

Primary source:

- Chai Wah Wu, *Computing the Greatest Common Divisor of Binomial Coefficients
  C(mn,mk)*, arXiv:2606.20940v2 (4 August 2026),
  https://arxiv.org/abs/2606.20940.

## Formalisation boundary

Mathlib already supplies Kummer's theorem and classical full-row binomial-gcd results.
A different binomial-gcd theorem was formally verified in Lean by Guo, Qiu, Cao, Feng
and Gao in 2026, for the object

[
D(k)=gcd_{2le qle k+1}inom{qk}{k},
]

whose upper row varies with `q`.

The audit located no prior Lean, Coq/Rocq, Isabelle or HOL formalisation of McTague's
arithmetic-progression restricted family or of the full minus-one valuation theorem
formalised here. The repository therefore says **"no prior equivalent formalisation
located"**, not **"first formalisation of binomial gcds"**.

Primary source:

- Dakai Guo, Ruichen Qiu, Yichuan Cao, Ruyong Feng, Xiao-Shan Gao,
  *A Greatest Common Divisor Criterion of Certain Binomial Coefficients*,
  arXiv:2606.22997, https://arxiv.org/abs/2606.22997.

Lean completeness establishes formal correctness of the stated theorems relative to
Lean/Mathlib. It does not by itself establish originality or priority.
