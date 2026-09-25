# Literature boundary

A final source-level novelty and priority audit was completed on
**25 September 2026**. The reproducible source comparison, theorem-level matrix,
search methodology, version checks, formalisation search, limitations, and bibliography
are in [the final September 2026 novelty audit](novelty-audit-2026-09.md).

## Current conclusion

The audit located **no mathematically equivalent prior theorem for the full
\(p\equiv-1\pmod m\) valuation formula** formalised as
**PascalMinusOne.minus_one_valuation**.

The supported public wording is:

> A source-level literature audit through 25 September 2026 located no equivalent prior
> theorem for the full \(p\equiv-1\pmod m\) valuation formula. McTague's Theorem Q
> gives the \(p\equiv1\pmod m\) branch, and the corrected arXiv v5 same-residue
> remark gives the one-parity minus-one branches \((A,B)=(m,0)\) and \((0,m)\)
> when \(p>m\). The audit located no equivalent prior theorem for the mixed-parity
> branch or for the general \(p=m-1\) regime.

This is a negative-search/apparent-extension claim, not an unconditional priority
claim. The repository does not claim "first theorem", "first proof", or "first
formalisation".

## Exact McTague boundary

Carl McTague's Theorem Q studies exactly the same restricted gcd family, after
\(n=N\) and \(q=m\):

\[
\gcd_{0<k<n/q}\binom n{qk}.
\]

For \(p\equiv1\pmod q\) it gives valuation \(1\) exactly when the base-\(p\)
digit sum \(\alpha_p(n)\le q\). Under the project's hypothesis \(m\mid N\),
\(\alpha_p(N)\equiv N\equiv0\pmod m\), so
\(\alpha_p(N)\le m\) is equivalent to \(\alpha_p(N)=m\). Thus the project's
plus-one theorem is mathematically McTague's theorem after a straightforward
translation.

The first remark on page 2 of the **corrected v5** preprint weakens the
\(p\equiv1\pmod q\) hypothesis to, for example:

- \(p>q\);
- \(\gcd(p,q)=1\); and
- all powers in a minimal power-sum expansion of \(n\) having the same residue
  modulo \(q\).

For \(p\equiv-1\pmod m\), even powers have residue \(+1\) and odd powers have
residue \(-1\). Therefore the corrected remark directly gives the project's
one-parity valuation-1 cases \((A,B)=(m,0)\) and \((0,m)\) when \(p>m\).

It does **not** give:

- the mixed \((A,B)=(1,1)\) branch, because both residue classes occur;
- any \(p=m-1\) case, because corrected v5 requires \(p>q=m\).

This version point matters. arXiv v4 used broader-looking wording ("\(p\) and \(q\)
being relatively prime"); v5 adds \(p>q\), and the arXiv record explicitly says the
first remark on page 2 was corrected.

McTague also records

\[
v_2\!\left(\gcd_{0<k<2}\binom6{3k}\right)=2,
\]

the project's \(m=3,p=2=m-1,N=6\), \((A,B)=(1,1)\) instance. Thus the
existence of a valuation-2 exception is prior art; no general \(p=m-1\)
classification was located.

Primary source:

- Carl McTague, *On the Greatest Common Divisor of Binomial Coefficients
  C(n,q), C(n,2q), C(n,3q), ...*, American Mathematical Monthly 124(4)
  (2017), 353--356, DOI 10.4169/amer.math.monthly.124.4.353,
  corrected arXiv:1510.06696v5 (25 July 2018),
  https://arxiv.org/abs/1510.06696.

## Wu 2026

Chai Wah Wu defines

\[
g(m,n)=\gcd_{1\le k<n}\binom{mn}{mk},
\]

so \(g(m,n)=G(mn;m)\): it is the same gcd object.

Wu's Theorem 1 uses the standard Kummer carry-shift observation for a prime-power
modulus. This confirms that the project's scaling theorem should be treated primarily
as reusable formal infrastructure rather than an independent mathematical novelty.

Wu's Theorem 2 assumes a prime-power modulus and that every relevant non-modulus prime
is congruent to \(1\pmod m\). It therefore excludes, rather than classifies, the
general \(p\equiv-1\pmod m\) regime.

Primary source:

- Chai Wah Wu, *Computing the Greatest Common Divisor of Binomial Coefficients
  C(mn,mk)*, arXiv:2606.20940v2 (4 August 2026),
  https://arxiv.org/abs/2606.20940.

## Formalisation boundary

A different binomial-gcd theorem was formally verified in Lean by Guo, Qiu, Cao, Feng
and Gao in 2026. Their object is

\[
D(k)=\gcd_{2\le q\le k+1}\binom{qk}{k},
\]

where the lower index is fixed and the upper row varies. Their Section 3 gives the
actual Lean predicate and theorem.

The final audit located no prior Lean, Coq/Rocq, Isabelle or HOL formalisation of
McTague's arithmetic-progression fixed-row family or of the minus-one valuation theorem
formalised here. The defensible claim is therefore **"no prior equivalent
formalisation located"**, not **"first formalisation of binomial gcds"**.

Primary source:

- Dakai Guo, Ruichen Qiu, Yichuan Cao, Ruyong Feng, Xiao-Shan Gao,
  *A Greatest Common Divisor Criterion of Certain Binomial Coefficients*,
  arXiv:2606.22997, https://arxiv.org/abs/2606.22997.

## Contribution boundary for the paper

The paper should treat the components as follows:

| Component | Literature boundary |
| --- | --- |
| full minus-one theorem | no equivalent prior theorem located; strict subfamilies known |
| mixed \((1,1),p>m\) | no equivalent prior theorem located |
| mixed \((1,1),p=m-1\) | isolated McTague example known; no general theorem located |
| one-parity \(p>m\) | directly covered by corrected McTague v5 |
| one-parity \(p=m-1\) | no equivalent prior theorem located |
| plus-one theorem | known from McTague after straightforward translation |
| scaling | standard Kummer carry-shift mechanism; not a headline novelty claim |
| complete \(m=3,4,6\) formulas | applications/corollaries; no identical complete formulas located |
| proof-assistant formalisation of this family | no equivalent formalisation located |

Lean completeness and Palomar registration are verification and provenance facts. They
are not evidence of mathematical novelty or historical priority.
