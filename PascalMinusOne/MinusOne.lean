import PascalMinusOne.Basic
import PascalMinusOne.Digits
import PascalMinusOne.Kummer
import PascalMinusOne.SignedTokens
import Mathlib.Data.Nat.Digits.Div

namespace PascalMinusOne

/-- Piecewise value predicted by the `p ≡ -1 (mod m)` theorem. -/
def minusOneExpectedValuation (m p A B : ℕ) : ℕ :=
  if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
  else if A = 1 ∧ B = 1 ∧ m < p then 1
  else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
  else 0

/-- Convert `p % m = m-1` into alternating signs for powers of `p`. -/
theorem pow_mod_eq_parity_sign {m p i : ℕ} (hm : 2 ≤ m) (hpm : p % m = m - 1) :
    p ^ i % m = if Even i then 1 else m - 1 := by
  have hpmod : p ≡ m - 1 [MOD m] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    exact hpm
  have hsq : (m - 1) ^ 2 ≡ 1 [MOD m] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < m)]
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    have hm2 : m - 2 + 2 = m := Nat.sub_add_cancel hm
    have heq : (m - 1) ^ 2 = m * (m - 2) + 1 := by
      nlinarith
    rw [heq]
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (by omega : 1 < m)]
  by_cases hi : Even i
  · rw [if_pos hi]
    obtain ⟨j, rfl⟩ := hi
    have hpow : p ^ (j + j) ≡ 1 [MOD m] := by
      calc
        p ^ (j + j) ≡ (m - 1) ^ (j + j) [MOD m] := hpmod.pow _
        _ = ((m - 1) ^ 2) ^ j := by rw [← two_mul j, pow_mul]
        _ ≡ 1 ^ j [MOD m] := hsq.pow j
        _ = 1 := by simp
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < m)] using hpow
  · rw [if_neg hi]
    have hodd : Odd i := Nat.not_even_iff_odd.mp hi
    obtain ⟨j, rfl⟩ := hodd
    have hpow : p ^ (2 * j + 1) ≡ m - 1 [MOD m] := by
      calc
        p ^ (2 * j + 1) ≡ (m - 1) ^ (2 * j + 1) [MOD m] := hpmod.pow _
        _ = ((m - 1) ^ 2) ^ j * (m - 1) := by
          rw [pow_add, pow_one, pow_mul]
        _ ≡ 1 ^ j * (m - 1) [MOD m] := (hsq.pow j).mul Nat.ModEq.rfl
        _ = m - 1 := by simp
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : m - 1 < m)] using hpow

/-- Evaluating a little-endian digit list at base `-1` gives its even-position sum minus
its odd-position sum. -/
lemma ofDigits_neg_one_eq_parityDigitSums (L : List ℕ) :
    Nat.ofDigits (-1 : ℤ) L =
      ((parityDigitSums L).1 : ℤ) - ((parityDigitSums L).2 : ℤ) := by
  induction L with
  | nil => simp [Nat.ofDigits, parityDigitSums]
  | cons d ds ih =>
      simp [Nat.ofDigits, parityDigitSums, ih]
      ring

/-- Divisibility by `m` is the signed zero-sum condition on the even/odd base-`p`
digit totals when `p ≡ -1 (mod m)`. -/
lemma dvd_iff_signedZeroSum_digitSums {m p k : ℕ}
    (hm : 2 ≤ m) (hpm : p % m = m - 1) :
    m ∣ k ↔ SignedZeroSum m (evenDigitSum p k) (oddDigitSum p k) := by
  have hpmod : p ≡ m - 1 [MOD m] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    exact hpm
  have hmp1 : m ∣ p + 1 := by
    rw [← Nat.modEq_zero_iff_dvd]
    have h := hpmod.add_right 1
    simpa [Nat.ModEq, Nat.sub_add_cancel (by omega : 1 ≤ m)] using h
  have hdiv : (m : ℤ) ∣ (p : ℤ) - (-1 : ℤ) := by
    rw [sub_neg_eq_add]
    exact_mod_cast hmp1
  simpa [SignedZeroSum, evenDigitSum, oddDigitSum,
    ofDigits_neg_one_eq_parityDigitSums] using
    (Nat.dvd_iff_dvd_ofDigits m p (-1 : ℤ) hdiv k)

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
