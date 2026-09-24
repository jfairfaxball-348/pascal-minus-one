import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace PascalMinusOne

/-- `A` positive and `B` negative unit tokens sum to zero modulo `m`. -/
def SignedZeroSum (m A B : ℕ) : Prop :=
  (m : ℤ) ∣ (A : ℤ) - (B : ℤ)

/-- A nonempty proper signed submultiset has zero sum modulo `m`. -/
def HasProperZeroSubmultiset (m A B : ℕ) : Prop :=
  ∃ a b : ℕ,
    a ≤ A ∧ b ≤ B ∧
    0 < a + b ∧ a + b < A + B ∧
    SignedZeroSum m a b

/-- Minimal nonempty zero-sum multiset made from `A` copies of `+1` and `B` copies of `-1`. -/
def MinimalSignedZeroSum (m A B : ℕ) : Prop :=
  0 < A + B ∧ SignedZeroSum m A B ∧ ¬ HasProperZeroSubmultiset m A B

@[simp] theorem signedZeroSum_one_one (m : ℕ) : SignedZeroSum m 1 1 := by
  simp [SignedZeroSum]

@[simp] theorem signedZeroSum_m_zero (m : ℕ) : SignedZeroSum m m 0 := by
  simp [SignedZeroSum]

@[simp] theorem signedZeroSum_zero_m (m : ℕ) : SignedZeroSum m 0 m := by
  simp [SignedZeroSum]

/-- TODO(Tokens-1): the complete classification of minimal zero-sum `±1` multisets. -/
theorem minimal_signed_zero_sum_classification {m A B : ℕ} (hm : 3 ≤ m) :
    MinimalSignedZeroSum m A B ↔
      (A = 1 ∧ B = 1) ∨ (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) := by
  sorry

end PascalMinusOne
