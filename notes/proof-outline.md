# Proof outline

The formalisation now has four theorem layers:

1. the `p ≡ -1 (mod m)` valuation theorem;
2. the `p ≡ 1 (mod m)` valuation theorem needed by the project;
3. the common prime-power scaling reduction;
4. complete prime-by-prime valuation corollaries for `m = 3,4,6`.

## Minus-one layer

For `m ≥ 3`, `m ∣ N`, `m < N`, prime `p), and
`p % m = m - 1`, the proof of `minus_one_valuation` proceeds as follows.

1. **Kummer / carries.** Mathlib provides `padicValNat_choose`, expressing the valuation
   of `Nat.choose` as a carry count. The local bridge
   `padicVal_choose_eq_zero_iff_digitwiseLE` is proved via prefix remainders and absence
   of carries.
2. **Signed tokens.** Even base-`p` exponents contribute `+1` and odd exponents
   contribute `-1` modulo `m`. Proper no-borrow choices correspond to proper
   zero-sum signed submultisets.
3. **Minimal zero-sum classification.** The theorem
   `minimal_signed_zero_sum_classification` proves that, for `m ≥ 3`, the only
   minimal zero-sum multisets over `±1` are `(1,1)`, `(m,0)`, and `(0,m)`.
4. **Uniform cases.** For `p > m`, use the high-digit one-borrow construction. For the
   edge case `p = m-1`, use the repaired witness `p^(t-1) + p^s`, with `s < t`
   another occupied exponent of the same parity.
5. **Mixed case, `p > m`.** Reduce to two occupied opposite-parity powers and construct
   a one-borrow witness.
6. **Exceptional mixed case, `p = m-1`.** Exclude one borrow using the
   `m`-identical-token argument, then construct an exact two-borrow witness.
7. **Assemble the gcd valuation.** `padicVal_G_eq_of_lower_bound_of_witness` turns the
   lower bound plus an exact witness into the valuation of the restricted gcd.

## Plus-one layer

The theorem `plus_one_valuation` assumes `0 < m`, `m ∣ N`, `m < N`,
`p.Prime`, and `p % m = 1 % m`. It proves that the valuation is `1` exactly when
the base-`p` digit sum of `N` equals `m), and is `0` otherwise.

The proof is internal to Lean and does not import a literature result as an axiom.

1. **Digit-sum congruence.** Since `p ≡ 1 (mod m)`, divisibility by `m` is equivalent
   to divisibility of the base-`p` digit sum.
2. **Non-minimal digit sum.** If the digit sum is strictly larger than `m`, choose a
   componentwise subdigit list with total exactly `m`. It gives a proper admissible
   no-borrow index, hence valuation `0`.
3. **Minimal digit sum.** If the digit sum is exactly `m`, a valuation-`0` admissible
   index would have positive digit sum divisible by `m` but strictly below `m`, a
   contradiction. Thus every admissible coefficient has valuation at least `1`.
4. **Exact one-carry witness.** Write the final two base-`p` digits as `a,d` with
   `d>0`. Lower `d` by one, raise `a` by one, and pair the resulting number with a
   complementary digit `p-1` in the adjacent place. The two numbers add to `N`;
   the digit-sum form of Kummer gives valuation exactly `1`.

## Scaling layer

`scaling_valuation` removes a common factor `p^c` from both arguments:

[
v_p(G(p^cN';p^cq))=v_p(G(N';q)).
]

The proof uses `Nat.digits_base_pow_mul` to show digit-sum invariance under trailing
base-`p` zeros, the digit-sum form of Kummer to preserve individual binomial
valuations, and an exact correspondence between scaled and unscaled admissible indices.
It also handles the degenerate empty-index cases.

## Small-modulus layer

For `m=3,4,6`, every prime not dividing the modulus lies in one of the residue classes
`±1` modulo `m`. The remaining prime divisors of the modulus are reduced by
`scaling_valuation`.

- **`m=3`.** `p=3` scales to modulus `1`; every other prime is `1` or `-1`
  modulo `3`.
- **`m=4`.** `p=2` scales to modulus `1`; every odd prime is `1` or `-1`
  modulo `4`.
- **`m=6`.** `p=2` scales to modulus `3`, where the minus-one theorem applies;
  `p=3` scales to modulus `2`, where the plus-one theorem applies; every other prime
  is `1` or `-1` modulo `6`.

This yields the public theorems `modulus_three_valuation`,
`modulus_four_valuation`, and `modulus_six_valuation`.

## Formalisation status

The initial scaffold contained 11 explicit theorem placeholders. All have been
eliminated. The current project Lean sources contain no `sorry`, `admit`, or
replacement `axiom` declarations.

The Lean proofs, rather than the finite checks, determine proof status. The Python
regression tests and reference sweep remain independent debugging/evidence checks.
