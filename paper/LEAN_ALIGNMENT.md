# Paper / Lean alignment note

Date: 25 September 2026.

This note checks the mathematical statements in `paper/main.tex` against the public Lean theorem layer at repository commit `d4a8d4c93c5dda22829774857c13df81d17fb989`.

## Principal theorem

Paper theorem: Theorem 1.1, minus-one valuation formula.

Lean theorem: `PascalMinusOne.minus_one_valuation` in `PascalMinusOne/MinusOne.lean`.

Lean declaration:

```lean
theorem minus_one_valuation
    {m N p : Nat}
    (hm : 3 <= m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N)
```

The paper states exactly the same hypotheses in conventional notation: `m >= 3`, `m | N`, `m < N`, `p` prime, and `p congruent to -1 modulo m`. The paper explicitly notes that Lean represents the congruence as `p % m = m - 1`.

The paper's four valuation branches match `minusOneExpectedValuation`:

```lean
if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
else if A = 1 ∧ B = 1 ∧ m < p then 1
else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
else 0
```

where `A = evenDigitSum p N` and `B = oddDigitSum p N`.

## Restricted gcd definition

Lean definition:

```lean
def admissibleIndices (N m : Nat) : Finset Nat :=
  (Finset.range N).filter fun k => 0 < k ∧ m ∣ k

def G (N m : Nat) : Nat :=
  (admissibleIndices N m).gcd fun k => N.choose k
```

The paper uses `G(N;m)=gcd{binom(N,k): 0<k<N, m|k}`, matching `Finset.range N` together with `0 < k`.

## Plus-one theorem

Paper theorem: Theorem 7.1.

Lean theorem: `PascalMinusOne.plus_one_valuation`.

Lean hypotheses: `0 < m`, `p.Prime`, `p % m = 1 % m`, `m ∣ N`, `m < N`.

Paper statement matches these hypotheses and states the same branch condition using the ordinary base-`p` digit sum: valuation `1` exactly when the digit sum is `m`, otherwise `0`.

## Scaling theorem

Paper theorem: Theorem 8.1.

Lean theorem: `PascalMinusOne.scaling_valuation`.

Lean declaration:

```lean
theorem scaling_valuation
    {p c q N' : Nat} (hp : p.Prime) :
    padicValNat p (G (p ^ c * N') (p ^ c * q)) =
      padicValNat p (G N' q)
```

The paper states the same equality and does not add extra hypotheses.

## Small-modulus corollaries

Paper corollaries: Corollaries 9.1, 9.2, and 9.3.

Lean theorems:

- `PascalMinusOne.modulus_three_valuation`: hypotheses `p.Prime`, `3 ∣ N`, `3 < N`.
- `PascalMinusOne.modulus_four_valuation`: hypotheses `p.Prime`, `4 ∣ N`, `4 < N`.
- `PascalMinusOne.modulus_six_valuation`: hypotheses `p.Prime`, `6 ∣ N`, `6 < N`.

The paper states those same hypotheses and uses the same dispatch pattern as the Lean definitions:

- modulus 3: `p=3` scales to modulus 1, otherwise residues `1` and `-1` mod 3;
- modulus 4: `p=2` scales to modulus 1, otherwise residues `1` and `-1` mod 4;
- modulus 6: `p=2` scales to modulus 3, `p=3` scales to modulus 2, otherwise residues `1` and `-1` mod 6.

## Result

No overstatement relative to the Lean theorem layer was found in the final paper source. The paper uses conventional notation and explanatory lemmas, but the named theorem statements match the Lean hypotheses, branch conditions, digit definitions, and restricted-gcd definition.
