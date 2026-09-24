import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace PascalMinusOne

/-- Indices occurring in the restricted gcd: positive multiples of `m` below `N`. -/
def admissibleIndices (N m : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k ↦ 0 < k ∧ m ∣ k

/-- The restricted gcd of binomial coefficients. -/
def G (N m : ℕ) : ℕ :=
  (admissibleIndices N m).gcd fun k ↦ N.choose k

/-- Predicate version of membership in `admissibleIndices`. -/
def Admissible (N m k : ℕ) : Prop :=
  0 < k ∧ k < N ∧ m ∣ k

@[simp] theorem mem_admissibleIndices_iff {N m k : ℕ} :
    k ∈ admissibleIndices N m ↔ Admissible N m k := by
  simp only [admissibleIndices, Finset.mem_filter, Finset.mem_range, Admissible]
  constructor
  · rintro ⟨hkN, hkpos, hmk⟩
    exact ⟨hkpos, hkN, hmk⟩
  · rintro ⟨hkpos, hkN, hmk⟩
    exact ⟨hkN, hkpos, hmk⟩

theorem m_mem_admissibleIndices {N m : ℕ} (hm : 0 < m) (hmN : m < N) :
    m ∈ admissibleIndices N m := by
  simp [admissibleIndices, hm, hmN]

theorem G_dvd_choose {N m k : ℕ} (hk : k ∈ admissibleIndices N m) :
    G N m ∣ N.choose k := by
  exact Finset.gcd_dvd hk

/-- The restricted gcd is nonzero as soon as the admissible set contains the index `m`. -/
theorem G_ne_zero {N m : ℕ} (hm : 0 < m) (hNm : m < N) :
    G N m ≠ 0 := by
  rw [G, Finset.gcd_ne_zero_iff]
  refine ⟨m, m_mem_admissibleIndices hm hNm, ?_⟩
  exact Nat.choose_ne_zero_iff.mpr hNm.le

/-- If every admissible binomial coefficient has `p`-adic valuation at least `r`,
and one admissible coefficient has valuation exactly `r`, then the restricted gcd
has valuation exactly `r`. -/
theorem padicVal_G_eq_of_lower_bound_of_witness
    {N m p r : ℕ} (hm : 0 < m) (hNm : m < N) (hp : p.Prime)
    (hlower :
      ∀ k, Admissible N m k → r ≤ padicValNat p (N.choose k))
    (hwitness :
      ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = r) :
    padicValNat p (G N m) = r := by
  letI : Fact p.Prime := ⟨hp⟩
  have hGne : G N m ≠ 0 := G_ne_zero hm hNm
  apply Nat.le_antisymm
  · obtain ⟨k, hkadm, hkval⟩ := hwitness
    have hkMem : k ∈ admissibleIndices N m :=
      mem_admissibleIndices_iff.mpr hkadm
    have hGdvd : G N m ∣ N.choose k :=
      G_dvd_choose hkMem
    by_contra hnot
    have hlt : r < padicValNat p (G N m) :=
      Nat.lt_of_not_ge hnot
    have hpG : p ^ (r + 1) ∣ G N m :=
      (padicValNat_dvd_iff_le hGne).2 hlt
    have hpChoose : p ^ (r + 1) ∣ N.choose k :=
      hpG.trans hGdvd
    have hchooseNe : N.choose k ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr hkadm.2.1.le
    have hle : r + 1 ≤ padicValNat p (N.choose k) :=
      (padicValNat_dvd_iff_le hchooseNe).1 hpChoose
    rw [hkval] at hle
    exact (Nat.not_succ_le_self r) (by
      simpa [Nat.succ_eq_add_one] using hle)
  · rw [← padicValNat_dvd_iff_le hGne]
    rw [G, Finset.dvd_gcd_iff]
    intro k hk
    have hkadm : Admissible N m k :=
      mem_admissibleIndices_iff.mp hk
    have hchooseNe : N.choose k ≠ 0 :=
      Nat.choose_ne_zero_iff.mpr hkadm.2.1.le
    exact (padicValNat_dvd_iff_le hchooseNe).2 (hlower k hkadm)

end PascalMinusOne
