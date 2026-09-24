import PascalMinusOne.PlusOne
import PascalMinusOne.Scaling

namespace PascalMinusOne

/-!
# Complete valuation formulas for the small moduli 3, 4, and 6

For primes not dividing the modulus, every reduced residue class modulo
`3`, `4`, or `6` is `±1`, so the plus-one and minus-one valuation
theorems cover all cases.  When the prime divides the modulus, the scaling
theorem removes exactly the prime-power part appearing in the modulus and
reduces to modulus `1`, `2`, or `3`.
-/

/-- The explicit valuation formula for modulus `3`. -/
def modulusThreeExpectedValuation (p N : ℕ) : ℕ :=
  if p = 3 then
    plusOneExpectedValuation 1 p (N / 3)
  else if p % 3 = 1 then
    plusOneExpectedValuation 3 p N
  else
    minusOneExpectedValuation 3 p (evenDigitSum p N) (oddDigitSum p N)

/-- The explicit valuation formula for modulus `4`. -/
def modulusFourExpectedValuation (p N : ℕ) : ℕ :=
  if p = 2 then
    plusOneExpectedValuation 1 p (N / 4)
  else if p % 4 = 1 then
    plusOneExpectedValuation 4 p N
  else
    minusOneExpectedValuation 4 p (evenDigitSum p N) (oddDigitSum p N)

/-- The explicit valuation formula for modulus `6`. -/
def modulusSixExpectedValuation (p N : ℕ) : ℕ :=
  if p = 2 then
    minusOneExpectedValuation 3 p
      (evenDigitSum p (N / 2)) (oddDigitSum p (N / 2))
  else if p = 3 then
    plusOneExpectedValuation 2 p (N / 3)
  else if p % 6 = 1 then
    plusOneExpectedValuation 6 p N
  else
    minusOneExpectedValuation 6 p (evenDigitSum p N) (oddDigitSum p N)

private lemma prime_mod_three_eq_one_or_two
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hlt : p % 3 < 3 := Nat.mod_lt _ (by omega)
  by_cases h1 : p % 3 = 1
  · exact Or.inl h1
  by_cases h2 : p % 3 = 2
  · exact Or.inr h2
  have h0 : p % 3 = 0 := by omega
  have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
  have hEq : 3 = p :=
    (Nat.dvd_prime_two_le hp (by omega)).1 hd
  exact (hp3 hEq.symm).elim

private lemma prime_mod_four_eq_one_or_three
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hlt : p % 4 < 4 := Nat.mod_lt _ (by omega)
  by_cases h1 : p % 4 = 1
  · exact Or.inl h1
  by_cases h3 : p % 4 = 3
  · exact Or.inr h3
  have hrem : p % 4 = 0 ∨ p % 4 = 2 := by omega
  have h2dvd : 2 ∣ p := by
    rcases hrem with h0 | h2
    · have hdecomp := Nat.mod_add_div p 4
      refine ⟨2 * (p / 4), ?_⟩
      omega
    · have hdecomp := Nat.mod_add_div p 4
      refine ⟨2 * (p / 4) + 1, ?_⟩
      omega
  have hEq : 2 = p :=
    (Nat.dvd_prime_two_le hp (by omega)).1 h2dvd
  exact (hp2 hEq.symm).elim

private lemma prime_mod_six_eq_one_or_five
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by omega)
  by_cases h1 : p % 6 = 1
  · exact Or.inl h1
  by_cases h5 : p % 6 = 5
  · exact Or.inr h5
  have hrem :
      p % 6 = 0 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 := by
    omega
  rcases hrem with h0 | h2 | h3 | h4
  · have hdecomp := Nat.mod_add_div p 6
    have h2dvd : 2 ∣ p := by
      refine ⟨3 * (p / 6), ?_⟩
      omega
    have hEq : 2 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h2dvd
    exact (hp2 hEq.symm).elim
  · have hdecomp := Nat.mod_add_div p 6
    have h2dvd : 2 ∣ p := by
      refine ⟨3 * (p / 6) + 1, ?_⟩
      omega
    have hEq : 2 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h2dvd
    exact (hp2 hEq.symm).elim
  · have hdecomp := Nat.mod_add_div p 6
    have h3dvd : 3 ∣ p := by
      refine ⟨2 * (p / 6) + 1, ?_⟩
      omega
    have hEq : 3 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h3dvd
    exact (hp3 hEq.symm).elim
  · have hdecomp := Nat.mod_add_div p 6
    have h2dvd : 2 ∣ p := by
      refine ⟨3 * (p / 6) + 2, ?_⟩
      omega
    have hEq : 2 = p :=
      (Nat.dvd_prime_two_le hp (by omega)).1 h2dvd
    exact (hp2 hEq.symm).elim

/-- Complete prime-by-prime valuation formula for `G(N;3)`. -/
theorem modulus_three_valuation
    {p N : ℕ} (hp : p.Prime) (h3N : 3 ∣ N) (hN : 3 < N) :
    padicValNat p (G N 3) = modulusThreeExpectedValuation p N := by
  by_cases hp3 : p = 3
  · subst p
    rcases h3N with ⟨n, rfl⟩
    have hn : 1 < n := by omega
    have hscale :=
      scaling_valuation (p := 3) (c := 1) (q := 1) (N' := n) hp
    have hplus :=
      plus_one_valuation (m := 1) (p := 3) (N := n)
        (by omega) hp (by simp) (Nat.one_dvd n) hn
    rw [modulusThreeExpectedValuation, if_pos rfl]
    have hs :
        padicValNat 3 (G (3 * n) 3) =
          padicValNat 3 (G n 1) := by
      simpa using hscale
    have hdiv : (3 * n) / 3 = n := by
      simpa [Nat.mul_comm] using (Nat.mul_div_left n (by omega : 0 < 3))
    rw [hdiv]
    exact hs.trans hplus
  · rcases prime_mod_three_eq_one_or_two hp hp3 with h1 | h2
    · rw [modulusThreeExpectedValuation, if_neg hp3, if_pos h1]
      exact
        plus_one_valuation (m := 3) (p := p) (N := N)
          (by omega) hp (by simpa using h1) h3N hN
    · have hnot1 : p % 3 ≠ 1 := by omega
      rw [modulusThreeExpectedValuation, if_neg hp3, if_neg hnot1]
      exact
        minus_one_valuation (m := 3) (N := N) (p := p)
          (by omega) h3N hN hp (by simpa using h2)

/-- Complete prime-by-prime valuation formula for `G(N;4)`. -/
theorem modulus_four_valuation
    {p N : ℕ} (hp : p.Prime) (h4N : 4 ∣ N) (hN : 4 < N) :
    padicValNat p (G N 4) = modulusFourExpectedValuation p N := by
  by_cases hp2 : p = 2
  · subst p
    rcases h4N with ⟨n, rfl⟩
    have hn : 1 < n := by omega
    have hscale :=
      scaling_valuation (p := 2) (c := 2) (q := 1) (N' := n) hp
    have hplus :=
      plus_one_valuation (m := 1) (p := 2) (N := n)
        (by omega) hp (by simp) (Nat.one_dvd n) hn
    rw [modulusFourExpectedValuation, if_pos rfl]
    have hs :
        padicValNat 2 (G (4 * n) 4) =
          padicValNat 2 (G n 1) := by
      simpa using hscale
    have hdiv : (4 * n) / 4 = n := by
      simpa [Nat.mul_comm] using (Nat.mul_div_left n (by omega : 0 < 4))
    rw [hdiv]
    exact hs.trans hplus
  · rcases prime_mod_four_eq_one_or_three hp hp2 with h1 | h3
    · rw [modulusFourExpectedValuation, if_neg hp2, if_pos h1]
      exact
        plus_one_valuation (m := 4) (p := p) (N := N)
          (by omega) hp (by simpa using h1) h4N hN
    · have hnot1 : p % 4 ≠ 1 := by omega
      rw [modulusFourExpectedValuation, if_neg hp2, if_neg hnot1]
      exact
        minus_one_valuation (m := 4) (N := N) (p := p)
          (by omega) h4N hN hp (by simpa using h3)

/-- Complete prime-by-prime valuation formula for `G(N;6)`. -/
theorem modulus_six_valuation
    {p N : ℕ} (hp : p.Prime) (h6N : 6 ∣ N) (hN : 6 < N) :
    padicValNat p (G N 6) = modulusSixExpectedValuation p N := by
  by_cases hp2 : p = 2
  · subst p
    rcases h6N with ⟨n, rfl⟩
    have hn : 1 < n := by omega
    have hscale :=
      scaling_valuation (p := 2) (c := 1) (q := 3) (N' := 3 * n) hp
    have hminus :=
      minus_one_valuation (m := 3) (N := 3 * n) (p := 2)
        (by omega) (Nat.dvd_mul_right 3 n) (by omega) hp (by decide)
    rw [modulusSixExpectedValuation, if_pos rfl]
    have hs :
        padicValNat 2 (G (6 * n) 6) =
          padicValNat 2 (G (3 * n) 3) := by
      have hNscale : 2 ^ 1 * (3 * n) = 6 * n := by
        simp only [pow_one]
        omega
      have hMscale : 2 ^ 1 * 3 = 6 := by decide
      rw [hNscale, hMscale] at hscale
      exact hscale
    have hdiv : (6 * n) / 2 = 3 * n := by omega
    rw [hdiv]
    exact hs.trans hminus
  · by_cases hp3 : p = 3
    · subst p
      rcases h6N with ⟨n, rfl⟩
      have hn : 1 < n := by omega
      have hscale :=
        scaling_valuation (p := 3) (c := 1) (q := 2) (N' := 2 * n) hp
      have hplus :=
        plus_one_valuation (m := 2) (p := 3) (N := 2 * n)
          (by omega) hp (by decide) (Nat.dvd_mul_right 2 n) (by omega)
      rw [modulusSixExpectedValuation, if_neg hp2, if_pos rfl]
      have hs :
          padicValNat 3 (G (6 * n) 6) =
            padicValNat 3 (G (2 * n) 2) := by
        have hNscale : 3 ^ 1 * (2 * n) = 6 * n := by
          simp only [pow_one]
          omega
        have hMscale : 3 ^ 1 * 2 = 6 := by decide
        rw [hNscale, hMscale] at hscale
        exact hscale
      have hdiv : (6 * n) / 3 = 2 * n := by omega
      rw [hdiv]
      exact hs.trans hplus
    · rcases prime_mod_six_eq_one_or_five hp hp2 hp3 with h1 | h5
      · rw [modulusSixExpectedValuation, if_neg hp2, if_neg hp3, if_pos h1]
        exact
          plus_one_valuation (m := 6) (p := p) (N := N)
            (by omega) hp (by simpa using h1) h6N hN
      · have hnot1 : p % 6 ≠ 1 := by omega
        rw [modulusSixExpectedValuation, if_neg hp2, if_neg hp3, if_neg hnot1]
        exact
          minus_one_valuation (m := 6) (N := N) (p := p)
            (by omega) h6N hN hp (by simpa using h5)

end PascalMinusOne
