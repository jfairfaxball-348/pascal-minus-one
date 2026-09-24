# Proof outline

The target is `PascalMinusOne.minus_one_valuation` for `m ≥ 3`, `m ∣ N`, `m < N`, prime `p`, and `p % m = m - 1`.

## Layers

1. **Kummer / carries.** Mathlib already provides `padicValNat_choose`, expressing the valuation of `Nat.choose` as a carry count. We wrap it as `padicVal_choose_eq_carryCount`. The missing local bridge is the zero-borrow digitwise criterion.
2. **Signed tokens.** Even base-`p` exponents contribute `+1` and odd exponents contribute `-1` modulo `m`. Proper no-borrow choices correspond to proper zero-sum signed submultisets.
3. **Minimal zero-sum classification.** For `m ≥ 3`, the only minimal zero-sum multisets over `±1` are `(1,1)`, `(m,0)`, and `(0,m)`.
4. **Uniform cases.** Produce a one-borrow witness. For `p > m`, use the high-digit construction from the hand proof. For `p = m-1`, use the repaired witness `p^(t-1) + p^s`, where `s < t` is another occupied exponent of the same parity.
5. **Mixed case, `p > m`.** Reduce to two occupied opposite-parity powers and construct a one-borrow witness.
6. **Exceptional mixed case, `p = m-1`.** Exclude one borrow using the `m` identical-token argument, then construct a two-borrow witness.
7. **Scaling.** Remove a common factor `p^c` from both `N` and `m` by trailing-zero invariance of carries.

## Scaffold proof gaps

There are **11 explicit `sorry` occurrences** in the initial scaffold:

- `Kummer.lean`: `padicVal_choose_eq_zero_iff_digitwiseLE`.
- `SignedTokens.lean`: `minimal_signed_zero_sum_classification`.
- `MinusOne.lean`: `pow_mod_eq_parity_sign`, `noBorrow_iff_proper_signed_zero_sum`, `uniform_case_one_borrow_of_gt`, `uniform_case_one_borrow_edge`, `mixed_case_one_borrow_of_gt`, `exceptional_mixed_no_one_borrow`, `exceptional_mixed_two_borrow_witness`, `minus_one_valuation`.
- `Scaling.lean`: `scaling_valuation`.

That list totals 11 theorem names, matching the mechanically checked initial count. The repository CI reports the count on every run.

No theorem with a `sorry` should be described as formally verified.
