import PascalMinusOne

/-!
# Pascal Minus-One GCD: proved Solution surface

The definitions are repeated exactly as in `Challenge.lean` so Comparator can
check their values as well as the theorem type. The proof then bridges those
definitions to the already-proved project theorem
`PascalMinusOne.minus_one_valuation`; no mathematical argument is re-proved
here.
-/

namespace PascalMinusOnePalomar

def G (N m : ℕ) : ℕ :=
  ((Finset.range N).filter fun k ↦ 0 < k ∧ m ∣ k).gcd fun k ↦ N.choose k

def parityDigitSums : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | d :: ds =>
      let tail := parityDigitSums ds
      (d + tail.2, tail.1)

def evenDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).1

def oddDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).2

def minusOneExpectedValuation (m p A B : ℕ) : ℕ :=
  if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
  else if A = 1 ∧ B = 1 ∧ m < p then 1
  else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
  else 0

private theorem G_eq_project (N m : ℕ) :
    G N m = PascalMinusOne.G N m := by
  rfl

private theorem parityDigitSums_eq_project (L : List ℕ) :
    parityDigitSums L = PascalMinusOne.parityDigitSums L := by
  induction L with
  | nil => rfl
  | cons d ds ih =>
      simp [parityDigitSums, PascalMinusOne.parityDigitSums, ih]

private theorem evenDigitSum_eq_project (p N : ℕ) :
    evenDigitSum p N = PascalMinusOne.evenDigitSum p N := by
  simp [evenDigitSum, PascalMinusOne.evenDigitSum, parityDigitSums_eq_project]

private theorem oddDigitSum_eq_project (p N : ℕ) :
    oddDigitSum p N = PascalMinusOne.oddDigitSum p N := by
  simp [oddDigitSum, PascalMinusOne.oddDigitSum, parityDigitSums_eq_project]

private theorem minusOneExpectedValuation_eq_project (m p A B : ℕ) :
    minusOneExpectedValuation m p A B =
      PascalMinusOne.minusOneExpectedValuation m p A B := by
  rfl

theorem minus_one_valuation
    {m N p : ℕ}
    (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) := by
  simpa only [G_eq_project, evenDigitSum_eq_project, oddDigitSum_eq_project,
    minusOneExpectedValuation_eq_project] using
    (PascalMinusOne.minus_one_valuation
      (m := m) (N := N) (p := p) hm hmN hNm hp hpm)

end PascalMinusOnePalomar
