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

/-- The two parity digit totals add to the ordinary digit sum. -/
lemma parityDigitSums_add_eq_sum (L : List ℕ) :
    (parityDigitSums L).1 + (parityDigitSums L).2 = L.sum := by
  induction L with
  | nil => rfl
  | cons d ds ih =>
      simp [parityDigitSums, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A suffix of zero digits does not change the even/odd digit totals. -/
lemma parityDigitSums_append_replicate_zero (L : List ℕ) (n : ℕ) :
    parityDigitSums (L ++ List.replicate n 0) = parityDigitSums L := by
  have hzero : ∀ r : ℕ, parityDigitSums (List.replicate r 0) = (0, 0) := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => simp [List.replicate_succ, parityDigitSums, ih]
  induction L with
  | nil => simpa using hzero n
  | cons d ds ih =>
      simp only [List.cons_append, parityDigitSums_cons, ih]

/-- Padding a base-`p` digit list to a fixed length leaves its parity totals unchanged. -/
lemma parityDigitSums_digitsAppend (p l n : ℕ) :
    parityDigitSums (Nat.digitsAppend p l n) = parityDigitSums (Nat.digits p n) := by
  simp [Nat.digitsAppend, parityDigitSums_append_replicate_zero]

/-- Componentwise-bounded digit lists have componentwise-bounded parity totals. -/
lemma parityDigitSums_mono {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) :
    (parityDigitSums S).1 ≤ (parityDigitSums D).1 ∧
      (parityDigitSums S).2 ≤ (parityDigitSums D).2 := by
  induction h with
  | nil => simp [parityDigitSums]
  | @cons s d S D hsd htail ih =>
      simp only [parityDigitSums_cons, Prod.fst, Prod.snd]
      omega

/-- Any prescribed pair of parity totals below those of a digit list can be realised by
a componentwise-bounded digit list of the same length. -/
lemma exists_subdigits_with_parityDigitSums
    (D : List ℕ) {a b : ℕ}
    (ha : a ≤ (parityDigitSums D).1)
    (hb : b ≤ (parityDigitSums D).2) :
    ∃ S : List ℕ,
      List.Forall₂ (· ≤ ·) S D ∧ parityDigitSums S = (a, b) := by
  induction D generalizing a b with
  | nil =>
      simp [parityDigitSums] at ha hb
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst a
      subst b
      exact ⟨[], List.Forall₂.nil, rfl⟩
  | cons d D ih =>
      simp only [parityDigitSums_cons, Prod.fst, Prod.snd] at ha hb
      by_cases had : a ≤ d
      · obtain ⟨T, hT, hpar⟩ :=
          ih (a := b) (b := 0) hb (Nat.zero_le _)
        refine ⟨a :: T, List.Forall₂.cons had hT, ?_⟩
        simp [parityDigitSums, hpar]
      · have hda : d < a := Nat.lt_of_not_ge had
        have htail : a - d ≤ (parityDigitSums D).2 := by omega
        obtain ⟨T, hT, hpar⟩ := ih (a := b) (b := a - d) hb htail
        refine ⟨d :: T, List.Forall₂.cons (Nat.le_refl d) hT, ?_⟩
        simp [parityDigitSums, hpar]
        omega

/-- Componentwise comparison of equal-length digit lists is respected by `Nat.ofDigits`. -/
lemma ofDigits_le_of_forall₂ (p : ℕ) {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) :
    Nat.ofDigits p S ≤ Nat.ofDigits p D := by
  induction h with
  | nil => rfl
  | @cons s d S D hsd htail ih =>
      simp only [Nat.ofDigits]
      exact Nat.add_le_add hsd (Nat.mul_le_mul_left p ih)

/-- Componentwise comparison also compares ordinary digit sums. -/
lemma sum_le_of_forall₂ {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) : S.sum ≤ D.sum := by
  induction h with
  | nil => rfl
  | @cons s d S D hsd htail ih =>
      simp only [List.sum_cons]
      exact Nat.add_le_add hsd ih

/-- If two equal-length digit lists are componentwise ordered and not equal, their digit sums
are strictly ordered. -/
lemma sum_lt_of_forall₂_of_ne {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) (hne : S ≠ D) :
    S.sum < D.sum := by
  induction h with
  | nil => exact (hne rfl).elim
  | @cons s d S D hsd htail ih =>
      simp only [List.sum_cons]
      by_cases hsdEq : s = d
      · subst d
        have htailNe : S ≠ D := by
          intro hEq
          apply hne
          simp [hEq]
        exact Nat.add_lt_add_left (ih htailNe) s
      · have hslt : s < d := lt_of_le_of_ne hsd hsdEq
        have hsum : S.sum ≤ D.sum := sum_le_of_forall₂ htail
        omega

/-- The head of the `i`-fold tail, with default zero, is `List.getD i 0`. -/
lemma head_drop_eq_getD (L : List ℕ) (i : ℕ) :
    (L.drop i).head! = L.getD i 0 := by
  induction i generalizing L with
  | zero =>
      cases L <;> rfl
  | succ i ih =>
      cases L with
      | nil => simp
      | cons d D => simpa using ih (L := D)

/-- For a valid base-`p` digit list, `digitAt` of its `ofDigits` value recovers `getD`. -/
lemma digitAt_ofDigits_eq_getD {p i : ℕ} (hp : 2 ≤ p) (L : List ℕ)
    (hL : ∀ d ∈ L, d < p) :
    digitAt p (Nat.ofDigits p L) i = L.getD i 0 := by
  rw [digitAt, Nat.ofDigits_div_pow_eq_ofDigits_drop i (by omega) L hL,
    Nat.ofDigits_mod_eq_head!]
  have hhead : (L.drop i).head! < p := by
    by_cases hnil : L.drop i = []
    · simpa [hnil] using (show 0 < p by omega)
    · exact hL _ (List.mem_of_mem_drop (List.head!_mem_self hnil))
  rw [Nat.mod_eq_of_lt hhead, head_drop_eq_getD]

/-- A componentwise subdigit list inherits the base bound from the ambient digit list. -/
lemma all_lt_of_forall₂_le {S D : List ℕ} {p : ℕ}
    (h : List.Forall₂ (· ≤ ·) S D)
    (hD : ∀ d ∈ D, d < p) :
    ∀ s ∈ S, s < p := by
  revert hD
  induction h with
  | nil => simp
  | @cons s d S D hsd htail ih =>
      intro hD x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact lt_of_le_of_lt hsd (hD d List.mem_cons_self)
      · exact ih (fun y hy => hD y (List.mem_cons_of_mem d hy)) x hx

/-- Componentwise list comparison can be read through `getD`, including past the end. -/
lemma getD_le_of_forall₂ {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) (i : ℕ) :
    S.getD i 0 ≤ D.getD i 0 := by
  induction h generalizing i with
  | nil => simp
  | @cons s d S D hsd htail ih =>
      cases i with
      | zero => simpa using hsd
      | succ i => simpa using ih i

/-- A componentwise comparison of valid base-`p` digit lists gives `DigitwiseLE`
for the represented natural numbers. -/
lemma digitwiseLE_of_forall₂_ofDigits {p : ℕ} (hp : 2 ≤ p) {S D : List ℕ}
    (hSD : List.Forall₂ (· ≤ ·) S D)
    (hS : ∀ s ∈ S, s < p)
    (hD : ∀ d ∈ D, d < p) :
    DigitwiseLE p (Nat.ofDigits p S) (Nat.ofDigits p D) := by
  intro i
  rw [digitAt_ofDigits_eq_getD hp S hS, digitAt_ofDigits_eq_getD hp D hD]
  exact getD_le_of_forall₂ hSD i

/-- Digitwise containment is equivalent to componentwise containment after padding the smaller
digit list to the length of the ambient number. -/
lemma digitsAppend_forall₂_of_digitwiseLE {p k N : ℕ}
    (hp : 2 ≤ p) (hkn : k ≤ N) (hdigit : DigitwiseLE p k N) :
    List.Forall₂ (· ≤ ·)
      (Nat.digitsAppend p (Nat.digits p N).length k)
      (Nat.digits p N) := by
  have hkpow : k < p ^ (Nat.digits p N).length :=
    lt_of_le_of_lt hkn (Nat.lt_base_pow_length_digits p N hp.one_lt)
  have hlen :
      (Nat.digitsAppend p (Nat.digits p N).length k).length =
        (Nat.digits p N).length :=
    Nat.length_digitsAppend hp.one_lt _ hkpow
  have hS :
      ∀ s ∈ Nat.digitsAppend p (Nat.digits p N).length k, s < p :=
    fun s hs => Nat.lt_of_mem_digitsAppend hp.one_lt _ s hs
  have hD : ∀ d ∈ Nat.digits p N, d < p :=
    fun d hd => Nat.digits_lt_base hp.one_lt hd
  have hSval :
      Nat.ofDigits p (Nat.digitsAppend p (Nat.digits p N).length k) = k := by
    simp [Nat.digitsAppend]
  have hDval : Nat.ofDigits p (Nat.digits p N) = N :=
    Nat.ofDigits_digits p N
  refine List.forall₂_of_length_eq_of_get hlen ?_
  intro i hiS hiD
  have hgetD :
      (Nat.digitsAppend p (Nat.digits p N).length k).getD i 0 ≤
        (Nat.digits p N).getD i 0 := by
    rw [← digitAt_ofDigits_eq_getD hp _ hS, hSval,
      ← digitAt_ofDigits_eq_getD hp _ hD, hDval]
    exact hdigit i
  rw [List.getD_eq_get _ _ ⟨i, hiS⟩, List.getD_eq_get _ _ ⟨i, hiD⟩] at hgetD
  exact hgetD

/-- Removing any high zero digits from a valid base-`p` representation does not change its
parity digit totals. -/
lemma parityDigitSums_digits_ofDigits {p : ℕ} (hp : 2 ≤ p) {L : List ℕ}
    (hL : ∀ d ∈ L, d < p) :
    parityDigitSums (Nat.digits p (Nat.ofDigits p L)) = parityDigitSums L := by
  have hinv :
      Nat.digitsAppend p L.length (Nat.ofDigits p L) = L :=
    (Nat.setInvOn_digitsAppend_ofDigits hp.one_lt L.length).1 ⟨rfl, hL⟩
  calc
    parityDigitSums (Nat.digits p (Nat.ofDigits p L)) =
        parityDigitSums (Nat.digitsAppend p L.length (Nat.ofDigits p L)) :=
      (parityDigitSums_digitsAppend p L.length (Nat.ofDigits p L)).symm
    _ = parityDigitSums L := congrArg parityDigitSums hinv

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
