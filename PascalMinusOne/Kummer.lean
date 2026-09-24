import PascalMinusOne.Basic
import PascalMinusOne.Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace PascalMinusOne

/-- A carry across the `i`th base-`p` boundary in `k + (n-k)`. -/
def CarryAt (p n k i : ℕ) : Prop :=
  p ^ i ≤ k % p ^ i + (n - k) % p ^ i

/-- Number of carries below a supplied bound. -/
def carryCount (p n k b : ℕ) : ℕ :=
  ((Finset.Ico 1 b).filter fun i ↦ CarryAt p n k i).card

/-- Thin wrapper around Mathlib's Kummer theorem `padicValNat_choose`. -/
theorem padicVal_choose_eq_carryCount {p n k b : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) = carryCount p n k b := by
  simpa [carryCount, CarryAt] using (padicValNat_choose (p := p) (n := n) (k := k) (b := b) hkn hnb)

/-- Digitwise no-borrow condition, phrased arithmetically rather than by list indexing. -/
def DigitwiseLE (p k n : ℕ) : Prop :=
  ∀ i, digitAt p k i ≤ digitAt p n i

/-- TODO(Kummer-1): zero valuation iff every base-`p` digit of `k` lies below that of `n`. -/
theorem padicVal_choose_eq_zero_iff_digitwiseLE {p n k : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) :
    padicValNat p (n.choose k) = 0 ↔ DigitwiseLE p k n := by
  sorry

end PascalMinusOne
