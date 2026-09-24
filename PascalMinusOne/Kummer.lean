import PascalMinusOne.Basic
import PascalMinusOne.Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace PascalMinusOne

/-- A carry across the `i`th base-`p` boundary in `k + (n-k)`. -/
def CarryAt (p n k i : ℕ) : Prop :=
  p ^ i ≤ k % p ^ i + (n - k) % p ^ i

instance carryAtDecidable (p n k i : ℕ) : Decidable (CarryAt p n k i) := by
  unfold CarryAt
  infer_instance

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

/-- The remainder modulo the next power is the old remainder plus the next base-`p` digit. -/
lemma mod_pow_succ_eq_mod_add_digitAt (p x i : ℕ) :
    x % p ^ (i + 1) = x % p ^ i + p ^ i * digitAt p x i := by
  simpa [pow_succ, digitAt] using
    (Nat.mod_mul (a := p ^ i) (b := p) (x := x))

/-- Digitwise comparison is equivalent to comparison of every base-`p` prefix. -/
lemma digitwiseLE_iff_mod_pow_le {p k n : ℕ} (hp : 0 < p) :
    DigitwiseLE p k n ↔ ∀ i, k % p ^ i ≤ n % p ^ i := by
  constructor
  · intro hdigit i
    induction i with
    | zero => simp only [pow_zero, Nat.mod_one]
    | succ i ih =>
        rw [mod_pow_succ_eq_mod_add_digitAt, mod_pow_succ_eq_mod_add_digitAt]
        exact Nat.add_le_add ih (Nat.mul_le_mul_left _ (hdigit i))
  · intro hprefix i
    have hnext := hprefix (i + 1)
    rw [mod_pow_succ_eq_mod_add_digitAt, mod_pow_succ_eq_mod_add_digitAt] at hnext
    by_contra hdigit
    have hlt : digitAt p n i < digitAt p k i := Nat.lt_of_not_ge hdigit
    have hpow : 0 < p ^ i := pow_pos hp i
    have hnmod : n % p ^ i < p ^ i := Nat.mod_lt _ hpow
    have hstep :
        p ^ i * (digitAt p n i + 1) ≤ p ^ i * digitAt p k i :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hlt)
    have hnlt :
        n % p ^ i + p ^ i * digitAt p n i <
          p ^ i * (digitAt p n i + 1) := by
      calc
        n % p ^ i + p ^ i * digitAt p n i <
            p ^ i + p ^ i * digitAt p n i :=
          Nat.add_lt_add_right hnmod _
        _ = p ^ i * (digitAt p n i + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    have htotal :
        n % p ^ i + p ^ i * digitAt p n i <
          k % p ^ i + p ^ i * digitAt p k i :=
      hnlt.trans_le (hstep.trans (Nat.le_add_left _ _))
    exact (Nat.not_lt_of_ge hnext) htotal

/-- Absence of a carry across `p^i` is exactly prefix comparison modulo `p^i`. -/
lemma not_carryAt_iff_mod_pow_le {p n k i : ℕ} (hp : 0 < p) (hkn : k ≤ n) :
    ¬ CarryAt p n k i ↔ k % p ^ i ≤ n % p ^ i := by
  unfold CarryAt
  have hpow : 0 < p ^ i := pow_pos hp i
  have hnmod :
      n % p ^ i =
        (k % p ^ i + (n - k) % p ^ i) % p ^ i := by
    calc
      n % p ^ i = (k + (n - k)) % p ^ i := by
        rw [Nat.add_sub_of_le hkn]
      _ = (k % p ^ i + (n - k) % p ^ i) % p ^ i :=
        Nat.add_mod _ _ _
  constructor
  · intro hnocarry
    have hsum :
        k % p ^ i + (n - k) % p ^ i < p ^ i :=
      Nat.lt_of_not_ge hnocarry
    have hnmod' :
        n % p ^ i = k % p ^ i + (n - k) % p ^ i := by
      calc
        n % p ^ i =
            (k % p ^ i + (n - k) % p ^ i) % p ^ i := hnmod
        _ = k % p ^ i + (n - k) % p ^ i := Nat.mod_eq_of_lt hsum
    rw [hnmod']
    exact Nat.le_add_right _ _
  · intro hkmod hcarry
    have hklt : k % p ^ i < p ^ i := Nat.mod_lt _ hpow
    have hrlt : (n - k) % p ^ i < p ^ i := Nat.mod_lt _ hpow
    have hsum_lt_double :
        k % p ^ i + (n - k) % p ^ i < p ^ i + p ^ i :=
      Nat.add_lt_add hklt hrlt
    have hsum_lt_pow_add_k :
        k % p ^ i + (n - k) % p ^ i < p ^ i + k % p ^ i := by
      simpa [Nat.add_comm] using Nat.add_lt_add_left hrlt (k % p ^ i)
    have hsub_lt_pow :
        (k % p ^ i + (n - k) % p ^ i) - p ^ i < p ^ i :=
      Nat.sub_lt_left_of_lt_add hcarry hsum_lt_double
    have hsub_lt_k :
        (k % p ^ i + (n - k) % p ^ i) - p ^ i < k % p ^ i :=
      Nat.sub_lt_left_of_lt_add hcarry hsum_lt_pow_add_k
    have hsum_mod :
        (k % p ^ i + (n - k) % p ^ i) % p ^ i =
          (k % p ^ i + (n - k) % p ^ i) - p ^ i := by
      rw [Nat.mod_eq_sub_mod hcarry, Nat.mod_eq_of_lt hsub_lt_pow]
    have hnmod' :
        n % p ^ i =
          (k % p ^ i + (n - k) % p ^ i) - p ^ i :=
      hnmod.trans hsum_mod
    rw [hnmod'] at hkmod
    exact (Nat.not_le_of_gt hsub_lt_k) hkmod

/-- Zero valuation iff every base-`p` digit of `k` lies below that of `n`. -/
theorem padicVal_choose_eq_zero_iff_digitwiseLE {p n k : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) :
    padicValNat p (n.choose k) = 0 ↔ DigitwiseLE p k n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  constructor
  · intro hval
    rw [digitwiseLE_iff_mod_pow_le hp]
    intro i
    cases i with
    | zero => simp only [pow_zero, Nat.mod_one]
    | succ i =>
        let b := max (Nat.log p n + 1) (i + 2)
        have hnb : Nat.log p n < b := by
          dsimp [b]
          exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
        have hcount : carryCount p n k b = 0 := by
          rw [← padicVal_choose_eq_carryCount hkn hnb]
          exact hval
        have hall : ∀ j ∈ Finset.Ico 1 b, ¬ CarryAt p n k j := by
          exact Finset.card_filter_eq_zero_iff.mp (by
            simpa [carryCount] using hcount)
        have hib : i + 1 < b := by
          dsimp [b]
          exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
        have hnocarry : ¬ CarryAt p n k (i + 1) :=
          hall (i + 1) (by
            simp only [Finset.mem_Ico]
            exact ⟨Nat.succ_le_succ (Nat.zero_le _), hib⟩)
        exact
          (not_carryAt_iff_mod_pow_le (p := p) (n := n) (k := k) (i := i + 1) hp hkn).1
            hnocarry
  · intro hdigit
    have hprefix :
        ∀ i, k % p ^ i ≤ n % p ^ i :=
      (digitwiseLE_iff_mod_pow_le (p := p) (k := k) (n := n) hp).1 hdigit
    let b := Nat.log p n + 1
    have hnb : Nat.log p n < b := by
      dsimp [b]
      exact Nat.lt_succ_self _
    rw [padicVal_choose_eq_carryCount hkn hnb, carryCount,
      Finset.card_filter_eq_zero_iff]
    intro i hi
    exact
      (not_carryAt_iff_mod_pow_le (p := p) (n := n) (k := k) (i := i) hp hkn).2
        (hprefix i)

end PascalMinusOne
