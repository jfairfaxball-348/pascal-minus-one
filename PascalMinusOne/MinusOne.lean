import PascalMinusOne.Basic
import PascalMinusOne.Digits
import PascalMinusOne.Kummer
import PascalMinusOne.SignedTokens

namespace PascalMinusOne

/-- Piecewise value predicted by the `p ≡ -1 (mod m)` theorem. -/
def minusOneExpectedValuation (m p A B : ℕ) : ℕ :=
  if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
  else if A = 1 ∧ B = 1 ∧ m < p then 1
  else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
  else 0

/-- TODO(MinusOne-1): convert `p % m = m-1` into alternating signs for powers of `p`. -/
theorem pow_mod_eq_parity_sign {m p i : ℕ} (hm : 2 ≤ m) (hpm : p % m = m - 1) :
    p ^ i % m = if Even i then 1 else m - 1 := by
  sorry

/-- TODO(MinusOne-2): no-borrow admissible indices are proper zero-sum signed submultisets. -/
theorem noBorrow_iff_proper_signed_zero_sum
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1) (hmN : m ∣ N) :
    (∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 0) ↔
      HasProperZeroSubmultiset m (evenDigitSum p N) (oddDigitSum p N) := by
  sorry

/-- TODO(MinusOne-3): uniform token cases admit a one-borrow witness when `p > m`. -/
theorem uniform_case_one_borrow_of_gt
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p) (hmN : m ∣ N) (hNm : m < N)
    (huniform :
      (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
      (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  sorry

/-- TODO(MinusOne-4): repaired `p = m-1` uniform witness, avoiding the defective `m p^(t-1)` choice. -/
theorem uniform_case_one_borrow_edge
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (huniform :
      (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
      (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) :
    ∃ t s k,
      s < t ∧ Occupied p N t ∧ Occupied p N s ∧
      k = p ^ (t - 1) + p ^ s ∧
      Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  sorry

/-- TODO(MinusOne-5): mixed case has a one-borrow witness when `p > m`. -/
theorem mixed_case_one_borrow_of_gt
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  sorry

/-- TODO(MinusOne-6): in the exceptional mixed case, no admissible index has exactly one borrow. -/
theorem exceptional_mixed_no_one_borrow
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∀ k, Admissible N m k → padicValNat p (N.choose k) ≠ 1 := by
  sorry

/-- TODO(MinusOne-7): the exceptional mixed case admits a two-borrow witness. -/
theorem exceptional_mixed_two_borrow_witness
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 2 := by
  sorry

/-- Main target theorem for primes congruent to `-1` modulo `m`. -/
theorem minus_one_valuation
    {m N p : ℕ}
    (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) := by
  sorry

end PascalMinusOne
