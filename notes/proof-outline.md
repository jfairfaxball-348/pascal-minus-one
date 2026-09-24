# Proof outline

The target is `PascalMinusOne.minus_one_valuation` for `m ≥ 3`, `m ∣ N`, `m < N`, prime `p`, and `p % m = m - 1`.

## Layers

1. **Kummer / carries.** Mathlib provides `padicValNat_choose`, expressing the valuation of `Nat.choose` as a carry count. The local bridge `padicVal_choose_eq_zero_iff_digitwiseLE` is proved via prefix remainders and absence of carries.
2. **Signed tokens.** Even base-`p` exponents contribute `+1` and odd exponents contribute `-1` modulo `m`. Proper no-borrow choices correspond to proper zero-sum signed submultisets.
3. **Minimal zero-sum classification.** The classification `minimal_signed_zero_sum_classification` is proved: for `m ≥ 3`, the only minimal zero-sum multisets over `±1` are `(1,1)`, `(m,0)`, and `(0,m)`.
4. **Uniform cases.** Produce a one-borrow witness. For `p > m`, use the high-digit construction from the hand proof. For `p = m-1`, use the repaired witness `p^(t-1) + p^s`, where `s < t` is another occupied exponent of the same parity.
5. **Mixed case, `p > m`.** Reduce to two occupied opposite-parity powers and construct a one-borrow witness.
6. **Exceptional mixed case, `p = m-1`.** Exclude one borrow using the `m` identical-token argument, then construct a two-borrow witness.
7. **Scaling.** Remove a common factor `p^c` from both `N` and `m` by trailing-zero invariance of carries.

## Scaffold proof gaps

The initial scaffold contained **11 explicit `sorry` occurrences**. On the current proof branch, the Kummer and minimal signed zero-sum gaps have been eliminated, leaving **2 explicit `sorry` occurrences**:

- `MinusOne.lean`: `minus_one_valuation`.
- `Scaling.lean`: `scaling_valuation`.

The repository CI checks this count mechanically on every run.

No theorem with a `sorry` should be described as formally verified.
