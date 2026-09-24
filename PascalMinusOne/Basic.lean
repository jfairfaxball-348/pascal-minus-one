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

end PascalMinusOne
