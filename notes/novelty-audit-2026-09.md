# Novelty audit — September 2026

Audit cutoff: **25 September 2026**.

This note records the repository's source-level literature and formalisation audit. It is
about originality and prior art, not proof correctness. The advertised theorem layer is
independently Lean-complete.

## Executive conclusion

A source-level literature audit through September 2026 located **no mathematically
equivalent prior theorem for the full `p ≡ -1 (mod m)` valuation formula** formalised in
this repository.

The strongest defensible description is therefore:

> The minus-one theorem appears to extend known restricted binomial-gcd results. McTague's
> 2017 theorem and its same-residue weakening cover the `p ≡ 1 (mod m)` branch and
> substantial `p > m` subfamilies of the minus-one regime, but the audit located no prior
> theorem giving the full mixed-parity classification or the general `p = m - 1`
> classification proved here.

This is deliberately not a priority claim such as "first" or "new". Failure to locate an
equivalent theorem is evidence for apparent novelty, not proof of priority.

## Object

The repository studies

[
G(N;m)=gcdleft{inom Nk:0<k<N, mmid kight}.
]

For a prime `p ≡ -1 (mod m)`, write

[
N=sum_i d_i p^i,qquad
A=sum_{i	ext{ even}}d_i,qquad
B=sum_{i	ext{ odd}}d_i.
]

The formal theorem gives valuation

- `2` when `(A,B)=(1,1)` and `p=m-1`;
- `1` when `(A,B)=(1,1)` and `p>m`;
- `1` when `(A,B)=(m,0)` or `(0,m)`;
- `0` otherwise.

## Closest prior art: McTague

Carl McTague, *On the Greatest Common Divisor of Binomial Coefficients
C(n,q), C(n,2q), C(n,3q), ...*, American Mathematical Monthly 124(4) (2017),
353–356, DOI 10.4169/amer.math.monthly.124.4.353, arXiv:1510.06696v5.

Stable sources:

- https://arxiv.org/abs/1510.06696
- https://arxiv.org/pdf/1510.06696
- https://doi.org/10.4169/amer.math.monthly.124.4.353

McTague's Theorem Q studies exactly the same gcd family after the renaming
`n=N`, `q=m`:

[
gcd_{0<k<n/q}inom n{qk}.
]

For prime `p ≡ 1 (mod q)`, it gives exact `p`-adic valuation `1` when the
base-`p` digit sum `α_p(n)` is at most `q`, and valuation `0` otherwise.

Because `q | n` and `p ≡ 1 (mod q)`, the digit sum is congruent to `n` modulo
`q`. Hence `α_p(n) ≤ q` is equivalent here to `α_p(n)=q`. This is mathematically
the repository's plus-one branch. The plus-one theorem is therefore not claimed as a
new mathematical result.

### McTague's same-residue weakening and the minus-one theorem

The corrected first remark on page 2 of arXiv v5 weakens `p ≡ 1 (mod q)`. Among
other conditions, it permits `p>q`, `gcd(p,q)=1`, and requires all powers of `p`
occurring in a minimal power-sum expansion of `n` to have the same residue modulo
`q`.

For `p ≡ -1 (mod m)`,

[
p^iequiv(-1)^ipmod m.
]

Thus McTague's same-residue hypothesis is exactly the condition that the nonzero
base-`p` digits occur in one exponent parity only. Under the digit-sum bound and
`m|N`, this yields precisely the repository's cases

[
(A,B)=(m,0)quad	ext{or}quad(0,m)
]

when `p>m`.

Therefore these two valuation-`1` arms have genuine prior coverage; the full
minus-one theorem is not wholly disjoint from the literature.

The mixed case `(A,B)=(1,1)` uses both residue classes `+1` and `-1` modulo
`m`, so it is outside that same-residue hypothesis. The corrected remark also assumes
`p>m`, so it does not cover the low-prime case `p=m-1`.

### The valuation-2 phenomenon

McTague explicitly records the example

[
v_2!left(gcd_{0<k<2}inom6{3k}ight)=v_2inom63=2.
]

This is the repository's `m=3`, `p=2=m-1`, `N=6`, `(A,B)=(1,1)` instance.
Accordingly, the *existence* of a valuation-2 exception is not new.

What this audit did not locate is a prior theorem giving the general classification

[
p=m-1,qquad(A,B)=(1,1)
quadLongrightarrowquad
v_p(G(N;m))=2
]

for arbitrary admissible parameters.

## Wu 2026

Chai Wah Wu, *Computing the Greatest Common Divisor of Binomial Coefficients
C(mn,mk)*, arXiv:2606.20940v2 (4 August 2026).

Stable source:

- https://arxiv.org/abs/2606.20940
- https://arxiv.org/pdf/2606.20940

Wu defines

[
g(m,n)=gcd_{1le k<n}inom{mn}{mk},
]

so `g(m,n)` is exactly `G(mn;m)`.

Wu gives computable product formulas under hypotheses including prime-power moduli and
conditions that the relevant non-modulus primes are congruent to `1 (mod m)`. Those
hypotheses do not recover the general `p ≡ -1 (mod m)` theorem or its low-prime
valuation-2 branch.

Wu also uses the standard Kummer observation that multiplying both summands by a power
of the valuation prime shifts base-`p` digits without changing the number of carries.
For that reason the repository's scaling theorem is treated primarily as proof
infrastructure rather than as a headline novelty claim.

## Other nearby literature

The audit also checked representative results on different restricted binomial gcds:

- Siao Hong, *The greatest common divisor of certain binomial coefficients*,
  C. R. Math. 354(8) (2016), 756–761, DOI 10.1016/j.crma.2016.06.001:
  lower indices subject to a coprimality condition, not `m|k`.
- H. Joris, C. Oestreicher, J. Steinig, *The greatest common divisor of certain sets of
  binomial coefficients*, J. Number Theory 21(1) (1985), 101–119,
  DOI 10.1016/0022-314X(85)90013-7: consecutive blocks of a Pascal row.
- Gil Kaplan and Dan Levy, *GCD of Truncated Rows in Pascal's Triangle*, Integers 4
  (2004), A14: truncated/consecutive portions of rows.
- Chan-Liang Chung, Tse-Chung Yang, Kanglun Zhou, *The Greatest Common Divisor of Sets
  of Binomial Coefficients with Restrictions*, Contemporary Mathematics 6(1) (2025),
  971–985, DOI 10.37256/cm.6120255017: restrictions such as `gcd(n,k)=d`, a
  technically nearby but different selected set.

None of these inspected formulations determines the full arithmetic-progression gcd
`G(N;m)` in the minus-one regime.

## Formalisation novelty

Mathlib already formalises Kummer's theorem and the classical gcd of all interior
binomial coefficients of a row. These are foundations used by this project, not prior
formalisation of the present restricted gcd theorem.

Dakai Guo, Ruichen Qiu, Yichuan Cao, Ruyong Feng and Xiao-Shan Gao,
*A Greatest Common Divisor Criterion of Certain Binomial Coefficients*,
arXiv:2606.22997 (22 June 2026), includes a Lean formalisation of the different object

[
D(k)=gcd_{2le qle k+1}inom{qk}{k},
]

where the upper row varies with `q`.

Stable source:

- https://arxiv.org/abs/2606.22997

The September 2026 audit located no existing Lean, Coq/Rocq, Isabelle or HOL
formalisation of McTague's arithmetic-progression restricted family or of the full
minus-one valuation classification formalised here.

The appropriate claim is therefore:

> No prior proof-assistant formalisation of these restricted
> arithmetic-progression binomial-gcd valuation results was located in this audit.

The repository does **not** claim to contain the first formalisation of binomial-gcd
mathematics in general.

## Contribution map

| Component | Literature status after this audit |
| --- | --- |
| full minus-one valuation theorem | partially covered by McTague; no equivalent full theorem located |
| mixed `(A,B)=(1,1), p>m` branch | no equivalent prior theorem located |
| general `p=m-1` valuation-2 classification | isolated example known; no general theorem located |
| same-parity `(m,0)` / `(0,m)` branches for `p>m` | covered by McTague's same-residue weakening |
| plus-one theorem | known in essentially exact form from McTague |
| scaling theorem | standard Kummer carry-shift mechanism; not promoted as headline novelty |
| complete `m=3,4,6` corollaries | no identical complete formulas located; novelty derives mainly from the minus-one input |
| Lean formalisation of this family | no prior equivalent formalisation located |

## Public wording

The repository uses the following level of claim:

> A source-level literature audit through September 2026 located no equivalent prior
> theorem for the full `p ≡ -1 (mod m)` valuation formula. McTague's 2017 theorem and
> its same-residue weakening cover the `p ≡ 1 (mod m)` branch and part of the minus-one
> `p>m` regime, but not the mixed-parity branch or the general `p=m-1`
> classification proved here.

This wording may be strengthened to an explicit priority claim only after further
independent expert or referee confirmation.
