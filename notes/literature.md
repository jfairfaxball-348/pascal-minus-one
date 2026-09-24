# Literature boundary

This repository does **not** claim novelty.

The current working boundary from the discovery phase is:

- McTague's work addresses the `p ≡ 1 (mod q)` direction relevant to the plus-one
  branch. That branch is now proved internally in Lean in this repository, but its
  formalisation here is not presented as a new mathematical result.
- A later same-residue weakening uses a size hypothesis `p > q`. The example
  `v_2(gcd {binom(6,3k)}) = 2` records the obstruction when that size condition is
  dropped in the nearby formulation.
- Wu (2026) gives computable formulas under hypotheses involving prime-power moduli and
  relevant primes congruent to `1 mod m`; the existing repository notes do not treat
  that as settling the `-1 mod m` theorem formalised here.
- Nearby work also treats consecutive blocks, coprimality restrictions, central
  intervals, or conditions such as `gcd(N,k)=d`, rather than this exact restricted
  family.

The Lean-complete state of the repository establishes formal correctness of the stated
theorems relative to Lean/Mathlib; it does **not** establish originality or priority.
Before any publication-level novelty statement about the minus-one result, run a
dedicated source-level literature review with complete bibliographic data and verify
the scope of each comparison directly from the source.
