import PascalMinusOne.Basic
import PascalMinusOne.Digits
import PascalMinusOne.Kummer
import PascalMinusOne.SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD

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
  have hp1 : 1 < p := by omega
  have hkpow : k < p ^ (Nat.digits p N).length :=
    lt_of_le_of_lt hkn
      (Nat.lt_base_pow_length_digits (b := p) (m := N) hp1)
  have hlen :
      (Nat.digitsAppend p (Nat.digits p N).length k).length =
        (Nat.digits p N).length :=
    Nat.length_digitsAppend hp1 _ hkpow
  have hS :
      ∀ s ∈ Nat.digitsAppend p (Nat.digits p N).length k, s < p :=
    fun s hs => Nat.lt_of_mem_digitsAppend hp1 _ s hs
  have hD : ∀ d ∈ Nat.digits p N, d < p :=
    fun d hd => Nat.digits_lt_base hp1 hd
  have hSval :
      Nat.ofDigits p (Nat.digitsAppend p (Nat.digits p N).length k) = k := by
    rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
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
  rw [List.getD_eq_getElem _ _ hiS, List.getD_eq_getElem _ _ hiD] at hgetD
  exact hgetD

/-- Removing any high zero digits from a valid base-`p` representation does not change its
parity digit totals. -/
lemma parityDigitSums_digits_ofDigits {p : ℕ} (hp : 2 ≤ p) {L : List ℕ}
    (hL : ∀ d ∈ L, d < p) :
    parityDigitSums (Nat.digits p (Nat.ofDigits p L)) = parityDigitSums L := by
  have hinv :
      Nat.digitsAppend p L.length (Nat.ofDigits p L) = L :=
    (Nat.setInvOn_digitsAppend_ofDigits (by omega : 1 < p) L.length).1 ⟨rfl, hL⟩
  calc
    parityDigitSums (Nat.digits p (Nat.ofDigits p L)) =
        parityDigitSums (Nat.digitsAppend p L.length (Nat.ofDigits p L)) :=
      (parityDigitSums_digitsAppend p L.length (Nat.ofDigits p L)).symm
    _ = parityDigitSums L := congrArg parityDigitSums hinv

/-- No-borrow admissible indices are exactly proper zero-sum signed submultisets. -/
theorem noBorrow_iff_proper_signed_zero_sum
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1) (hmN : m ∣ N) :
    (∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 0) ↔
      HasProperZeroSubmultiset m (evenDigitSum p N) (oddDigitSum p N) := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨k, hkadm, hkval⟩
    rcases hkadm with ⟨hkpos, hkN, hmk⟩
    have hdigit : DigitwiseLE p k N :=
      (padicVal_choose_eq_zero_iff_digitwiseLE (p := p) (n := N) (k := k)
        (Nat.le_of_lt hkN)).1 hkval
    let S := Nat.digitsAppend p (Nat.digits p N).length k
    have hSD : List.Forall₂ (· ≤ ·) S (Nat.digits p N) := by
      dsimp [S]
      exact digitsAppend_forall₂_of_digitwiseLE hp.two_le (Nat.le_of_lt hkN) hdigit
    have hparS :
        parityDigitSums S = parityDigitSums (Nat.digits p k) := by
      dsimp [S]
      exact parityDigitSums_digitsAppend p (Nat.digits p N).length k
    have hmono := parityDigitSums_mono hSD
    unfold HasProperZeroSubmultiset
    refine ⟨evenDigitSum p k, oddDigitSum p k, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hmono.1
      rw [hparS] at h
      simpa [evenDigitSum] using h
    · have h := hmono.2
      rw [hparS] at h
      simpa [oddDigitSum] using h
    · have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
      have hdigits : Nat.digits p k ≠ [] :=
        Nat.digits_ne_nil_iff_ne_zero.mpr hkne
      have hsumpos : 0 < (Nat.digits p k).sum :=
        List.sum_pos_iff_exists_pos_nat.mpr
          ⟨(Nat.digits p k).getLast hdigits, List.getLast_mem hdigits,
            Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hkne)⟩
      simpa [evenDigitSum, oddDigitSum, parityDigitSums_add_eq_sum] using hsumpos
    · have hSval : Nat.ofDigits p S = k := by
        dsimp [S]
        rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
      have hSne : S ≠ Nat.digits p N := by
        intro hEq
        have hkEqN : k = N := by
          calc
            k = Nat.ofDigits p S := hSval.symm
            _ = Nat.ofDigits p (Nat.digits p N) := congrArg (Nat.ofDigits p) hEq
            _ = N := Nat.ofDigits_digits p N
        exact (Nat.ne_of_lt hkN) hkEqN
      have hsumlt := sum_lt_of_forall₂_of_ne hSD hSne
      rw [← parityDigitSums_add_eq_sum S,
        ← parityDigitSums_add_eq_sum (Nat.digits p N)] at hsumlt
      rw [hparS] at hsumlt
      simpa [evenDigitSum, oddDigitSum] using hsumlt
    · exact
        (dvd_iff_signedZeroSum_digitSums (m := m) (p := p) (k := k) (by omega) hpm).1 hmk
  · rintro ⟨a, b, ha, hb, hpos, hproper, hzero⟩
    have haD : a ≤ (parityDigitSums (Nat.digits p N)).1 := by
      simpa [evenDigitSum] using ha
    have hbD : b ≤ (parityDigitSums (Nat.digits p N)).2 := by
      simpa [oddDigitSum] using hb
    obtain ⟨S, hSD, hpar⟩ :=
      exists_subdigits_with_parityDigitSums (Nat.digits p N) haD hbD
    have hD : ∀ d ∈ Nat.digits p N, d < p :=
      fun d hd => Nat.digits_lt_base hp.one_lt hd
    have hS : ∀ s ∈ S, s < p :=
      all_lt_of_forall₂_le hSD hD
    let k := Nat.ofDigits p S
    have hkn : k ≤ N := by
      dsimp [k]
      calc
        Nat.ofDigits p S ≤ Nat.ofDigits p (Nat.digits p N) :=
          ofDigits_le_of_forall₂ p hSD
        _ = N := Nat.ofDigits_digits p N
    have hSne : S ≠ Nat.digits p N := by
      intro hEq
      have htot : evenDigitSum p N + oddDigitSum p N = a + b := by
        have hpair :=
          congrArg (fun q : ℕ × ℕ => q.1 + q.2) hpar
        simpa [hEq, evenDigitSum, oddDigitSum] using hpair
      omega
    have hkneN : k ≠ N := by
      intro hkEq
      apply hSne
      apply Nat.ofDigits_inj_of_len_eq hp.one_lt hSD.length_eq hS hD
      dsimp [k] at hkEq
      calc
        Nat.ofDigits p S = N := hkEq
        _ = Nat.ofDigits p (Nat.digits p N) := (Nat.ofDigits_digits p N).symm
    have hkN : k < N := lt_of_le_of_ne hkn hkneN
    have hsumS : S.sum = a + b := by
      calc
        S.sum = (parityDigitSums S).1 + (parityDigitSums S).2 :=
          (parityDigitSums_add_eq_sum S).symm
        _ = a + b := by rw [hpar]
    have hsumpos : 0 < S.sum := by omega
    have hsumle : S.sum ≤ Nat.ofDigits p S :=
      Nat.sum_le_ofDigits S (Nat.le_of_lt hp.one_lt)
    have hkpos : 0 < k := by
      dsimp [k]
      exact hsumpos.trans_le hsumle
    have hdigit0 :
        DigitwiseLE p (Nat.ofDigits p S) (Nat.ofDigits p (Nat.digits p N)) :=
      digitwiseLE_of_forall₂_ofDigits hp.two_le hSD hS hD
    have hdigit : DigitwiseLE p k N := by
      simpa [k, Nat.ofDigits_digits] using hdigit0
    have hparK :
        parityDigitSums (Nat.digits p k) = (a, b) := by
      dsimp [k]
      exact (parityDigitSums_digits_ofDigits hp.two_le hS).trans hpar
    have heven : evenDigitSum p k = a := by
      simpa [evenDigitSum] using congrArg Prod.fst hparK
    have hodd : oddDigitSum p k = b := by
      simpa [oddDigitSum] using congrArg Prod.snd hparK
    have hzeroK :
        SignedZeroSum m (evenDigitSum p k) (oddDigitSum p k) := by
      rw [heven, hodd]
      exact hzero
    have hmk : m ∣ k :=
      (dvd_iff_signedZeroSum_digitSums (m := m) (p := p) (k := k) (by omega) hpm).2 hzeroK
    have hkval : padicValNat p (N.choose k) = 0 :=
      (padicVal_choose_eq_zero_iff_digitwiseLE (p := p) (n := N) (k := k) hkn).2 hdigit
    exact ⟨k, ⟨hkpos, hkN, hmk⟩, hkval⟩

/-- A digit is bounded by the parity total containing its position. -/
lemma getD_le_parityDigitSums (L : List ℕ) (i : ℕ) :
    L.getD i 0 ≤
      if Even i then (parityDigitSums L).1 else (parityDigitSums L).2 := by
  induction L generalizing i with
  | nil =>
      simp [parityDigitSums]
  | cons d ds ih =>
      cases i with
      | zero =>
          simp [parityDigitSums]
      | succ i =>
          have h := ih i
          by_cases hi : Even i
          · simp [parityDigitSums, Nat.succ_eq_add_one, Nat.even_add_one, hi] at h ⊢
            exact h
          · simp [parityDigitSums, Nat.succ_eq_add_one, Nat.even_add_one, hi] at h ⊢
            omega

/-- The arithmetic digit accessor is bounded by the corresponding parity digit sum. -/
lemma digitAt_le_parityDigitSum {p N i : ℕ} (hp : 2 ≤ p) :
    digitAt p N i ≤
      if Even i then evenDigitSum p N else oddDigitSum p N := by
  have h := getD_le_parityDigitSums (Nat.digits p N) i
  rw [Nat.getD_digits N i hp] at h
  simpa [digitAt, evenDigitSum, oddDigitSum] using h

/-- In a uniform token case with `p > m`, placing the digit `m` immediately below
the leading occupied digit forces exactly one borrow. -/
theorem uniform_case_one_borrow_of_gt
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p) (hmN : m ∣ N) (hNm : m < N)
    (huniform :
      (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
      (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hNpos : 0 < N := by omega
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  let t := Nat.log p N
  have hpowle : p ^ t ≤ N := by
    dsimp [t]
    exact Nat.pow_log_le_self p hNne
  have hNlt : N < p ^ (t + 1) := by
    dsimp [t]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp1 N
  have hqone : 1 ≤ N / p ^ t := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp0 t)]
    simpa using hpowle
  have hqpos : 0 < N / p ^ t := by omega
  have hqlt : N / p ^ t < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
    simpa [pow_succ, Nat.mul_comm] using hNlt
  have htocc : 0 < digitAt p N t := by
    rw [digitAt, Nat.mod_eq_of_lt hqlt]
    exact hqpos
  have htdata : 1 ≤ t ∧ digitAt p N (t - 1) = 0 := by
    rcases huniform with hevenUniform | hoddUniform
    · rcases hevenUniform with ⟨heven, hodd⟩
      have htEven : Even t := by
        by_contra htNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_neg htNotEven, hodd] at hbound
        omega
      have htpos : 0 < t := by
        by_contra htNotPos
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos htNotPos
        have hNP : N < p := by
          simpa [ht0] using hNlt
        have hdigit0 : digitAt p N 0 = N := by
          simp [digitAt, Nat.mod_eq_of_lt hNP]
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := 0) hp2
        have hNle : N ≤ m := by
          simpa [hdigit0, heven] using hbound
        omega
      have ht1 : 1 ≤ t := by omega
      have hpredNotEven : ¬ Even (t - 1) := by
        have h := htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one] at h
        exact h
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_neg hpredNotEven, hodd] at hbound
      exact ⟨ht1, by omega⟩
    · rcases hoddUniform with ⟨heven, hodd⟩
      have htNotEven : ¬ Even t := by
        intro htEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_pos htEven, heven] at hbound
        omega
      have htpos : 0 < t := by
        by_contra htNotPos
        have ht0 : t = 0 := Nat.eq_zero_of_not_pos htNotPos
        apply htNotEven
        simp [ht0]
      have ht1 : 1 ≤ t := by omega
      have hpredEven : Even (t - 1) := by
        by_contra hpredNotEven
        apply htNotEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one]
        exact hpredNotEven
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_pos hpredEven, heven] at hbound
      exact ⟨ht1, by omega⟩
  rcases htdata with ⟨ht1, hpredzero⟩
  have hNmod : N % p ^ t = N % p ^ (t - 1) := by
    have h := mod_pow_succ_eq_mod_add_digitAt p N (t - 1)
    rw [Nat.sub_add_cancel ht1] at h
    simpa [hpredzero] using h
  have hNmodlt : N % p ^ t < p ^ (t - 1) := by
    rw [hNmod]
    exact Nat.mod_lt _ (pow_pos hp0 _)
  let k := m * p ^ (t - 1)
  have hpowpredpos : 0 < p ^ (t - 1) := pow_pos hp0 _
  have hkpos : 0 < k := by
    dsimp [k]
    exact Nat.mul_pos (by omega) hpowpredpos
  have hkltpow : k < p ^ t := by
    have hmul : m * p ^ (t - 1) < p * p ^ (t - 1) :=
      (Nat.mul_lt_mul_right hpowpredpos).2 hpmgt
    dsimp [k]
    calc
      m * p ^ (t - 1) < p * p ^ (t - 1) := hmul
      _ = p ^ (t - 1) * p := Nat.mul_comm _ _
      _ = p ^ ((t - 1) + 1) := (pow_succ p (t - 1)).symm
      _ = p ^ t := by rw [Nat.sub_add_cancel ht1]
  have hkN : k < N := hkltpow.trans_le hpowle
  have hkn : k ≤ N := hkN.le
  have hmk : m ∣ k := by
    dsimp [k]
    exact dvd_mul_right m _
  have hnocarry_of_lt {j : ℕ} (hjt : j < t) : ¬ CarryAt p N k j := by
    apply
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := j) hp0 hkn).2
    have hjle : j ≤ t - 1 := by omega
    have hdvd : p ^ j ∣ k := by
      dsimp [k]
      exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow p hjle) m
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    exact Nat.zero_le _
  have hpowpred_le_k : p ^ (t - 1) ≤ k := by
    dsimp [k]
    have hm1 : 1 ≤ m := by omega
    calc
      p ^ (t - 1) = 1 * p ^ (t - 1) := by simp
      _ ≤ m * p ^ (t - 1) := by
        exact Nat.mul_le_mul_right _ hm1
  have hcarry : CarryAt p N k t := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t) hp0 hkn).1 hnocarry
    rw [Nat.mod_eq_of_lt hkltpow] at hprefix
    exact (Nat.not_le_of_gt (hNmodlt.trans_le hpowpred_le_k)) hprefix
  have hfilter :
      ((Finset.Ico 1 (t + 1)).filter fun i ↦ CarryAt p N k i) = {t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hj1, hjlt⟩, hjcarry⟩
      have hjle : j ≤ t := Nat.lt_succ_iff.mp hjlt
      by_cases hjt : j = t
      · exact hjt
      · have hjlt' : j < t := by omega
        exact (hnocarry_of_lt hjlt' hjcarry).elim
    · intro hj
      subst j
      exact ⟨⟨ht1, Nat.lt_succ_self t⟩, hcarry⟩
  have hcount : carryCount p N k (t + 1) = 1 := by
    rw [carryCount, hfilter]
    simp
  have hval : padicValNat p (N.choose k) = 1 := by
    rw [padicVal_choose_eq_carryCount hkn (Nat.lt_succ_self t), hcount]
  exact ⟨k, ⟨hkpos, hkN, hmk⟩, hval⟩

/-- In the edge case `p = m-1`, the repaired witness uses the leading occupied
digit `t` and a lower occupied digit `s` of the same parity:
`k = p^(t-1) + p^s`. -/
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
  letI : Fact p.Prime := ⟨hp⟩
  have hm2 : 2 ≤ m := by omega
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hpmod : p % m = m - 1 := by
    rw [hpm, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hNpos : 0 < N := by omega
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  let t := Nat.log p N
  let L := Nat.digits p N
  have hpowle : p ^ t ≤ N := by
    dsimp [t]
    exact Nat.pow_log_le_self p hNne
  have hNlt : N < p ^ (t + 1) := by
    dsimp [t]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp1 N
  have hqone : 1 ≤ N / p ^ t := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp0 t)]
    simpa using hpowle
  have hqpos : 0 < N / p ^ t := by omega
  have hqlt : N / p ^ t < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
    simpa [pow_succ, Nat.mul_comm] using hNlt
  have htocc : Occupied p N t := by
    dsimp [Occupied, digitAt]
    rw [Nat.mod_eq_of_lt hqlt]
    exact hqpos
  have hLlen : L.length = t + 1 := by
    dsimp [L, t]
    exact Nat.length_digits p N hp1 hNne
  have htlen : t < L.length := by omega
  have hLsum : L.sum = m := by
    have hsum :
        evenDigitSum p N + oddDigitSum p N = L.sum := by
      simpa [L, evenDigitSum, oddDigitSum] using
        parityDigitSums_add_eq_sum L
    rcases huniform with h | h <;> omega
  have hgettop : L.getD t 0 = digitAt p N t := by
    dsimp [L]
    rw [Nat.getD_digits N t hp2]
    rfl
  have hdrop : L.drop t = [L.getD t 0] := by
    rw [List.drop_eq_getElem_cons htlen,
      ← List.getD_eq_getElem L 0 htlen,
      ← hLlen, List.drop_length]
  have hdecomp : (L.take t).sum + digitAt p N t = m := by
    have h := List.sum_take_add_sum_drop L t
    rw [hdrop, List.sum_singleton, hgettop, hLsum] at h
    exact h
  have htoplt : digitAt p N t < p := by
    simpa [digitAt] using Nat.mod_lt (N / p ^ t) hp0
  have hprefpos : 0 < (L.take t).sum := by
    omega
  obtain ⟨s, hsTake, hsposTake⟩ :=
    List.exists_mem_iff_getElem.mp
      (List.sum_pos_iff_exists_pos_nat.mp hprefpos)
  have htakeLen : (L.take t).length = t := by
    exact List.length_take_of_le htlen.le
  have hst : s < t := by
    rw [htakeLen] at hsTake
    exact hsTake
  have hslen : s < L.length := hst.trans htlen
  have hsposL : 0 < L[s] := by
    simpa only [List.getElem_take] using hsposTake
  have hsgetpos : 0 < L.getD s 0 := by
    rw [List.getD_eq_getElem L 0 hslen]
    exact hsposL
  have hsocc : Occupied p N s := by
    dsimp [Occupied]
    dsimp [L] at hsgetpos
    rw [Nat.getD_digits N s hp2] at hsgetpos
    exact hsgetpos
  have ht1 : 1 ≤ t := by omega
  have hsame : Even s ↔ Even t := by
    rcases huniform with hevenUniform | hoddUniform
    · rcases hevenUniform with ⟨heven, hodd⟩
      have htEven : Even t := by
        by_contra htNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_neg htNotEven, hodd] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hsEven : Even s := by
        by_contra hsNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := s) hp2
        rw [if_neg hsNotEven, hodd] at hbound
        have hspos : 0 < digitAt p N s := hsocc
        omega
      exact ⟨fun _ ↦ htEven, fun _ ↦ hsEven⟩
    · rcases hoddUniform with ⟨heven, hodd⟩
      have htNotEven : ¬ Even t := by
        intro htEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_pos htEven, heven] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hsNotEven : ¬ Even s := by
        intro hsEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := s) hp2
        rw [if_pos hsEven, heven] at hbound
        have hspos : 0 < digitAt p N s := hsocc
        omega
      constructor
      · intro hsEven
        exact (hsNotEven hsEven).elim
      · intro htEven
        exact (htNotEven htEven).elim
  have hs_succ_lt : s + 1 < t := by
    have hsle : s + 1 ≤ t := by omega
    by_contra hnot
    have heq : s + 1 = t := by omega
    have hflip : Even t ↔ ¬ Even s := by
      rw [← heq]
      exact Nat.even_add_one
    by_cases hsEven : Even s
    · exact (hflip.mp (hsame.mp hsEven)) hsEven
    · exact hsEven (hsame.mpr (hflip.mpr hsEven))
  have hsltpred : s < t - 1 := by omega
  have hpredzero : digitAt p N (t - 1) = 0 := by
    rcases huniform with hevenUniform | hoddUniform
    · rcases hevenUniform with ⟨heven, hodd⟩
      have htEven : Even t := by
        by_contra htNotEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_neg htNotEven, hodd] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hpredNotEven : ¬ Even (t - 1) := by
        have h := htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one] at h
        exact h
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_neg hpredNotEven, hodd] at hbound
      omega
    · rcases hoddUniform with ⟨heven, hodd⟩
      have htNotEven : ¬ Even t := by
        intro htEven
        have hbound :=
          digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
        rw [if_pos htEven, heven] at hbound
        have htpos : 0 < digitAt p N t := htocc
        omega
      have hpredEven : Even (t - 1) := by
        by_contra hpredNotEven
        apply htNotEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one]
        exact hpredNotEven
      have hbound :=
        digitAt_le_parityDigitSum (p := p) (N := N) (i := t - 1) hp2
      rw [if_pos hpredEven, heven] at hbound
      omega
  have hNmod : N % p ^ t = N % p ^ (t - 1) := by
    have h := mod_pow_succ_eq_mod_add_digitAt p N (t - 1)
    rw [Nat.sub_add_cancel ht1] at h
    simpa [hpredzero] using h
  have hNmodlt : N % p ^ t < p ^ (t - 1) := by
    rw [hNmod]
    exact Nat.mod_lt _ (pow_pos hp0 _)
  have hpow_s_lt_pred : p ^ s < p ^ (t - 1) := by
    exact Nat.pow_lt_pow_right hp1 hsltpred
  let k := p ^ (t - 1) + p ^ s
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hkltpow : k < p ^ t := by
    have hlt2 : p ^ (t - 1) + p ^ s < 2 * p ^ (t - 1) := by
      omega
    have h2p : 2 * p ^ (t - 1) ≤ p * p ^ (t - 1) := by
      exact Nat.mul_le_mul_right _ hp2
    dsimp [k]
    calc
      p ^ (t - 1) + p ^ s < 2 * p ^ (t - 1) := hlt2
      _ ≤ p * p ^ (t - 1) := h2p
      _ = p ^ (t - 1) * p := Nat.mul_comm _ _
      _ = p ^ ((t - 1) + 1) := (pow_succ p (t - 1)).symm
      _ = p ^ t := by rw [Nat.sub_add_cancel ht1]
  have hkN : k < N := hkltpow.trans_le hpowle
  have hkn : k ≤ N := hkN.le
  have hmk : m ∣ k := by
    rw [Nat.dvd_iff_mod_eq_zero]
    dsimp [k]
    rw [Nat.add_mod,
      pow_mod_eq_parity_sign hm2 hpmod,
      pow_mod_eq_parity_sign hm2 hpmod]
    by_cases htEven : Even t
    · have hsEven : Even s := hsame.mpr htEven
      have hpredNotEven : ¬ Even (t - 1) := by
        have h := htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one] at h
        exact h
      simp [hpredNotEven, hsEven, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    · have hsNotEven : ¬ Even s := by
        intro hsEven
        exact htEven (hsame.mp hsEven)
      have hpredEven : Even (t - 1) := by
        by_contra hpredNotEven
        apply htEven
        rw [← Nat.sub_add_cancel ht1, Nat.even_add_one]
        exact hpredNotEven
      rw [if_pos hpredEven, if_neg hsNotEven]
      rw [Nat.add_comm, Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self]
  have hsmodbase : p ^ s ≤ N % p ^ (s + 1) := by
    rw [mod_pow_succ_eq_mod_add_digitAt]
    have hspos : 0 < digitAt p N s := hsocc
    have hdigit : 1 ≤ digitAt p N s := by omega
    have hmul : p ^ s ≤ p ^ s * digitAt p N s := by
      calc
        p ^ s = p ^ s * 1 := by simp
        _ ≤ p ^ s * digitAt p N s := Nat.mul_le_mul_left _ hdigit
    exact hmul.trans (Nat.le_add_left _ _)
  have hsmodle {j : ℕ} (hsj : s < j) : p ^ s ≤ N % p ^ j := by
    have hs1j : s + 1 ≤ j := by omega
    have hdvd : p ^ (s + 1) ∣ p ^ j := Nat.pow_dvd_pow p hs1j
    have hrem :
        N % p ^ (s + 1) ≤ N % p ^ j := by
      calc
        N % p ^ (s + 1) = (N % p ^ j) % p ^ (s + 1) :=
          (Nat.mod_mod_of_dvd N hdvd).symm
        _ ≤ N % p ^ j := Nat.mod_le _ _
    exact hsmodbase.trans hrem
  have hnocarry_of_lt {j : ℕ} (hjt : j < t) : ¬ CarryAt p N k j := by
    apply
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := j) hp0 hkn).2
    by_cases hjs : j ≤ s
    · have hjpred : j ≤ t - 1 := by omega
      have hdvdk : p ^ j ∣ k := by
        dsimp [k]
        exact dvd_add
          (Nat.pow_dvd_pow p hjpred)
          (Nat.pow_dvd_pow p hjs)
      rw [Nat.mod_eq_zero_of_dvd hdvdk]
      exact Nat.zero_le _
    · have hsj : s < j := by omega
      have hjpred : j ≤ t - 1 := by omega
      have hdvdtop : p ^ j ∣ p ^ (t - 1) :=
        Nat.pow_dvd_pow p hjpred
      have hpslt : p ^ s < p ^ j :=
        Nat.pow_lt_pow_right hp1 hsj
      have hkmod : k % p ^ j = p ^ s := by
        dsimp [k]
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvdtop]
        simp [Nat.mod_eq_of_lt hpslt]
      rw [hkmod]
      exact hsmodle hsj
  have hpowpred_le_k : p ^ (t - 1) ≤ k := by
    dsimp [k]
    exact Nat.le_add_right _ _
  have hcarry : CarryAt p N k t := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t) hp0 hkn).1 hnocarry
    rw [Nat.mod_eq_of_lt hkltpow] at hprefix
    exact (Nat.not_le_of_gt (hNmodlt.trans_le hpowpred_le_k)) hprefix
  have hfilter :
      ((Finset.Ico 1 (t + 1)).filter fun i ↦ CarryAt p N k i) = {t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hj1, hjlt⟩, hjcarry⟩
      have hjle : j ≤ t := Nat.lt_succ_iff.mp hjlt
      by_cases hjt : j = t
      · exact hjt
      · have hjlt' : j < t := by omega
        exact (hnocarry_of_lt hjlt' hjcarry).elim
    · intro hj
      subst j
      exact ⟨⟨ht1, Nat.lt_succ_self t⟩, hcarry⟩
  have hcount : carryCount p N k (t + 1) = 1 := by
    rw [carryCount, hfilter]
    simp
  have hval : padicValNat p (N.choose k) = 1 := by
    rw [padicVal_choose_eq_carryCount hkn (Nat.lt_succ_self t), hcount]
  exact ⟨t, s, k, hst, htocc, hsocc, rfl, ⟨hkpos, hkN, hmk⟩, hval⟩

/-- A natural digit list with zero total digit mass evaluates to zero in every base. -/
lemma ofDigits_eq_zero_of_sum_eq_zero (p : ℕ) :
    ∀ L : List ℕ, L.sum = 0 → Nat.ofDigits p L = 0 := by
  intro L
  induction L with
  | nil =>
      simp
  | cons d ds ih =>
      intro hsum
      simp only [List.sum_cons] at hsum
      have hd : d = 0 := by omega
      have hds : ds.sum = 0 := by omega
      subst d
      simp [Nat.ofDigits_cons, ih hds]

/-- A little-endian natural digit list with total digit mass one is bounded by
its highest available place value. -/
lemma ofDigits_le_pow_length_pred_of_sum_eq_one {p : ℕ} (hp : 0 < p) :
    ∀ L : List ℕ, L.sum = 1 →
      Nat.ofDigits p L ≤ p ^ (L.length - 1) := by
  intro L
  induction L with
  | nil =>
      intro hsum
      simp at hsum
  | cons d ds ih =>
      intro hsum
      simp only [List.sum_cons] at hsum
      by_cases hd : d = 0
      · subst d
        have htail : ds.sum = 1 := by omega
        have hdsne : ds ≠ [] := by
          intro hnil
          subst ds
          simp at htail
        have hlen : 1 ≤ ds.length :=
          List.length_pos_iff_ne_nil.mpr hdsne
        have hih := ih htail
        simp only [Nat.ofDigits_cons, zero_add, List.length_cons]
        calc
          p * Nat.ofDigits p ds ≤ p * p ^ (ds.length - 1) :=
            Nat.mul_le_mul_left p hih
          _ = p ^ (ds.length - 1) * p := by rw [Nat.mul_comm]
          _ = p ^ ((ds.length - 1) + 1) := (pow_succ p (ds.length - 1)).symm
          _ = p ^ ds.length := by rw [Nat.sub_add_cancel hlen]
      · have hd1 : d = 1 := by
          have hdpos : 0 < d := Nat.pos_of_ne_zero hd
          omega
        have htail : ds.sum = 0 := by omega
        have hofd : Nat.ofDigits p ds = 0 :=
          ofDigits_eq_zero_of_sum_eq_zero p ds htail
        subst d
        simp only [Nat.ofDigits_cons, hofd, mul_zero, add_zero, List.length_cons]
        exact pow_pos hp ds.length

/-- In the mixed token case with `p > m`, the witness `m * p^(t-1)` creates
exactly one carry at the leading boundary. -/
theorem mixed_case_one_borrow_of_gt
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hNne : N ≠ 0 := by
    intro hN
    subst N
    simp at hmixed
  let t := Nat.log p N
  let L := Nat.digits p N
  have hpowle : p ^ t ≤ N := by
    dsimp [t]
    exact Nat.pow_log_le_self p hNne
  have hNlt : N < p ^ (t + 1) := by
    dsimp [t]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp1 N
  have hqone : 1 ≤ N / p ^ t := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp0 t)]
    simpa using hpowle
  have hqpos : 0 < N / p ^ t := by omega
  have hqlt : N / p ^ t < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
    simpa [pow_succ, Nat.mul_comm] using hNlt
  have htocc : Occupied p N t := by
    dsimp [Occupied, digitAt]
    rw [Nat.mod_eq_of_lt hqlt]
    exact hqpos
  have htdigit : digitAt p N t = 1 := by
    have hbound :=
      digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
    by_cases htEven : Even t
    · rw [if_pos htEven, hmixed.1] at hbound
      have htpos : 0 < digitAt p N t := htocc
      omega
    · rw [if_neg htEven, hmixed.2] at hbound
      have htpos : 0 < digitAt p N t := htocc
      omega
  have hLlen : L.length = t + 1 := by
    dsimp [L, t]
    exact Nat.length_digits p N hp1 hNne
  have htlen : t < L.length := by omega
  have hLsum : L.sum = 2 := by
    have hsum :
        evenDigitSum p N + oddDigitSum p N = L.sum := by
      simpa [L, evenDigitSum, oddDigitSum] using
        parityDigitSums_add_eq_sum L
    omega
  have hgettop : L.getD t 0 = digitAt p N t := by
    dsimp [L]
    rw [Nat.getD_digits N t hp2]
    rfl
  have hdrop : L.drop t = [L.getD t 0] := by
    rw [List.drop_eq_getElem_cons htlen,
      ← List.getD_eq_getElem L 0 htlen,
      ← hLlen, List.drop_length]
  have hdecomp : (L.take t).sum + digitAt p N t = 2 := by
    have h := List.sum_take_add_sum_drop L t
    rw [hdrop, List.sum_singleton, hgettop, hLsum] at h
    exact h
  have hprefsum : (L.take t).sum = 1 := by
    omega
  have ht1 : 1 ≤ t := by
    by_contra htNotPos
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos htNotPos
    simp [ht0] at hprefsum
  have htakeLen : (L.take t).length = t := by
    exact List.length_take_of_le htlen.le
  have hNmodle : N % p ^ t ≤ p ^ (t - 1) := by
    rw [Nat.self_mod_pow_eq_ofDigits_take t N hp2]
    have hbound :=
      ofDigits_le_pow_length_pred_of_sum_eq_one (p := p) hp0 (L.take t) hprefsum
    rw [htakeLen] at hbound
    exact hbound
  let k := m * p ^ (t - 1)
  have hpowpredpos : 0 < p ^ (t - 1) := pow_pos hp0 _
  have hkpos : 0 < k := by
    dsimp [k]
    exact Nat.mul_pos (by omega) hpowpredpos
  have hkltpow : k < p ^ t := by
    have hmul : m * p ^ (t - 1) < p * p ^ (t - 1) :=
      (Nat.mul_lt_mul_right hpowpredpos).2 hpmgt
    dsimp [k]
    calc
      m * p ^ (t - 1) < p * p ^ (t - 1) := hmul
      _ = p ^ (t - 1) * p := Nat.mul_comm _ _
      _ = p ^ ((t - 1) + 1) := (pow_succ p (t - 1)).symm
      _ = p ^ t := by rw [Nat.sub_add_cancel ht1]
  have hkN : k < N := hkltpow.trans_le hpowle
  have hkn : k ≤ N := hkN.le
  have hmk : m ∣ k := by
    dsimp [k]
    exact dvd_mul_right m _
  have hnocarry_of_lt {j : ℕ} (hjt : j < t) : ¬ CarryAt p N k j := by
    apply
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := j) hp0 hkn).2
    have hjle : j ≤ t - 1 := by omega
    have hdvd : p ^ j ∣ k := by
      dsimp [k]
      exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow p hjle) m
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    exact Nat.zero_le _
  have hpowpred_lt_k : p ^ (t - 1) < k := by
    dsimp [k]
    have hm1 : 1 < m := by omega
    calc
      p ^ (t - 1) = 1 * p ^ (t - 1) := by simp
      _ < m * p ^ (t - 1) :=
        (Nat.mul_lt_mul_right hpowpredpos).2 hm1
  have hcarry : CarryAt p N k t := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t) hp0 hkn).1 hnocarry
    rw [Nat.mod_eq_of_lt hkltpow] at hprefix
    exact (Nat.not_le_of_gt (hNmodle.trans_lt hpowpred_lt_k)) hprefix
  have hfilter :
      ((Finset.Ico 1 (t + 1)).filter fun i ↦ CarryAt p N k i) = {t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hj1, hjlt⟩, hjcarry⟩
      have hjle : j ≤ t := Nat.lt_succ_iff.mp hjlt
      by_cases hjt : j = t
      · exact hjt
      · have hjlt' : j < t := by omega
        exact (hnocarry_of_lt hjlt' hjcarry).elim
    · intro hj
      subst j
      exact ⟨⟨ht1, Nat.lt_succ_self t⟩, hcarry⟩
  have hcount : carryCount p N k (t + 1) = 1 := by
    rw [carryCount, hfilter]
    simp
  have hval : padicValNat p (N.choose k) = 1 := by
    rw [padicVal_choose_eq_carryCount hkn (Nat.lt_succ_self t), hcount]
  exact ⟨k, ⟨hkpos, hkN, hmk⟩, hval⟩

/-- A natural digit list of total mass one represents a single power of the base. -/
lemma exists_ofDigits_eq_pow_of_sum_eq_one (p : ℕ) :
    ∀ L : List ℕ, L.sum = 1 →
      ∃ i, i < L.length ∧ Nat.ofDigits p L = p ^ i := by
  intro L
  induction L with
  | nil =>
      intro hsum
      simp at hsum
  | cons d ds ih =>
      intro hsum
      simp only [List.sum_cons] at hsum
      by_cases hd : d = 0
      · subst d
        have htail : ds.sum = 1 := by omega
        obtain ⟨i, hi, hpow⟩ := ih htail
        refine ⟨i + 1, by simp; omega, ?_⟩
        simp only [Nat.ofDigits_cons, zero_add, hpow]
        rw [Nat.mul_comm]
        exact (pow_succ p i).symm
      · have hd1 : d = 1 := by
          have hdpos : 0 < d := Nat.pos_of_ne_zero hd
          omega
        have htail : ds.sum = 0 := by omega
        have hzero : Nat.ofDigits p ds = 0 :=
          ofDigits_eq_zero_of_sum_eq_zero p ds htail
        subst d
        refine ⟨0, by simp, ?_⟩
        simp [Nat.ofDigits_cons, hzero]

/-- Two nonzero coefficient blocks on same-parity powers cannot form a multiple of `m`
when their coefficient sum is strictly below `m` and `p ≡ -1 (mod m)`. -/
lemma not_dvd_add_same_parity_powers
    {m p a b u v : ℕ} (hm : 3 ≤ m) (hpm : p % m = m - 1)
    (hpos : 0 < a + b) (hlt : a + b < m)
    (hpar : Even u ↔ Even v) :
    ¬ m ∣ a * p ^ u + b * p ^ v := by
  intro hdvd
  have hpu := pow_mod_eq_parity_sign (m := m) (p := p) (i := u) (by omega) hpm
  have hpv := pow_mod_eq_parity_sign (m := m) (p := p) (i := v) (by omega) hpm
  have hpuMod :
      p ^ u ≡ (if Even u then 1 else m - 1) [MOD m] := by
    rw [Nat.ModEq, hpu]
    by_cases hu : Even u
    · simp [hu, Nat.mod_eq_of_lt (by omega : 1 < m)]
    · simp [hu, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hpvMod :
      p ^ v ≡ (if Even v then 1 else m - 1) [MOD m] := by
    rw [Nat.ModEq, hpv]
    by_cases hv : Even v
    · simp [hv, Nat.mod_eq_of_lt (by omega : 1 < m)]
    · simp [hv, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
  have hcomb :=
    (hpuMod.mul_left a).add (hpvMod.mul_left b)
  have hzero :
      a * p ^ u + b * p ^ v ≡ 0 [MOD m] :=
    hdvd.modEq_zero_nat
  have hrhs :=
    hcomb.symm.trans hzero
  have habdvd : m ∣ a + b := by
    by_cases hu : Even u
    · have hv : Even v := hpar.mp hu
      have hz : a + b ≡ 0 [MOD m] := by
        simpa [hu, hv] using hrhs
      exact Nat.modEq_zero_iff_dvd.mp hz
    · have hv : ¬ Even v := by
        intro hv
        exact hu (hpar.mpr hv)
      have hz :
          a * (m - 1) + b * (m - 1) ≡ 0 [MOD m] := by
        simpa [hu, hv] using hrhs
      have hprod : m ∣ (a + b) * (m - 1) := by
        rw [Nat.add_mul]
        exact Nat.modEq_zero_iff_dvd.mp hz
      have hcop : Nat.Coprime m (m - 1) := by
        rw [← Nat.coprime_sub_self_left (m := m - 1) (n := m) (by omega)]
        have hdiff : m - (m - 1) = 1 := by omega
        rw [hdiff]
        simp
      exact hcop.dvd_of_dvd_mul_right hprod
  have hmle : m ≤ a + b := Nat.le_of_dvd hpos habdvd
  omega

/-- In the mixed case the base-`p` expansion is exactly two unit powers, and
their exponents have opposite parity. -/
lemma mixed_eq_sum_two_powers
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hmN : m ∣ N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ s t, s < t ∧ N = p ^ s + p ^ t ∧ ¬ (Even s ↔ Even t) := by
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hNne : N ≠ 0 := by
    intro hN
    subst N
    simp at hmixed
  let t := Nat.log p N
  let L := Nat.digits p N
  have hpowle : p ^ t ≤ N := by
    dsimp [t]
    exact Nat.pow_log_le_self p hNne
  have hNlt : N < p ^ (t + 1) := by
    dsimp [t]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp1 N
  have hqone : 1 ≤ N / p ^ t := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp0 t)]
    simpa using hpowle
  have hqpos : 0 < N / p ^ t := by omega
  have hqlt : N / p ^ t < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
    simpa [pow_succ, Nat.mul_comm] using hNlt
  have htocc : Occupied p N t := by
    dsimp [Occupied, digitAt]
    rw [Nat.mod_eq_of_lt hqlt]
    exact hqpos
  have htdigit : digitAt p N t = 1 := by
    have hbound :=
      digitAt_le_parityDigitSum (p := p) (N := N) (i := t) hp2
    by_cases htEven : Even t
    · rw [if_pos htEven, hmixed.1] at hbound
      have htpos : 0 < digitAt p N t := htocc
      omega
    · rw [if_neg htEven, hmixed.2] at hbound
      have htpos : 0 < digitAt p N t := htocc
      omega
  have hqeq : N / p ^ t = 1 := by
    have h := htdigit
    dsimp [digitAt] at h
    rw [Nat.mod_eq_of_lt hqlt] at h
    exact h
  have hLlen : L.length = t + 1 := by
    dsimp [L, t]
    exact Nat.length_digits p N hp1 hNne
  have htlen : t < L.length := by omega
  have hLsum : L.sum = 2 := by
    have hsum :
        evenDigitSum p N + oddDigitSum p N = L.sum := by
      simpa [L, evenDigitSum, oddDigitSum] using
        parityDigitSums_add_eq_sum L
    omega
  have hgettop : L.getD t 0 = digitAt p N t := by
    dsimp [L]
    rw [Nat.getD_digits N t hp2]
    rfl
  have hdrop : L.drop t = [L.getD t 0] := by
    rw [List.drop_eq_getElem_cons htlen,
      ← List.getD_eq_getElem L 0 htlen,
      ← hLlen, List.drop_length]
  have hdecomp : (L.take t).sum + digitAt p N t = 2 := by
    have h := List.sum_take_add_sum_drop L t
    rw [hdrop, List.sum_singleton, hgettop, hLsum] at h
    exact h
  have hprefsum : (L.take t).sum = 1 := by
    omega
  have htakeLen : (L.take t).length = t := by
    exact List.length_take_of_le htlen.le
  obtain ⟨s, hslen, hprefixpow⟩ :=
    exists_ofDigits_eq_pow_of_sum_eq_one p (L.take t) hprefsum
  have hst : s < t := by
    rw [htakeLen] at hslen
    exact hslen
  have hmod : N % p ^ t = p ^ s := by
    rw [Nat.self_mod_pow_eq_ofDigits_take t N hp2]
    simpa [L] using hprefixpow
  have hNpow : N = p ^ s + p ^ t := by
    calc
      N = N % p ^ t + p ^ t * (N / p ^ t) :=
        (Nat.mod_add_div N (p ^ t)).symm
      _ = p ^ s + p ^ t := by rw [hmod, hqeq]; simp
  have hopposite : ¬ (Even s ↔ Even t) := by
    intro hsame
    have hbad :=
      not_dvd_add_same_parity_powers
        (m := m) (p := p) (a := 1) (b := 1) (u := s) (v := t)
        hm hpm (by omega) (by omega) hsame
    apply hbad
    rw [one_mul, one_mul, ← hNpow]
    exact hmN
  exact ⟨s, t, hst, hNpow, hopposite⟩

/-- In the exceptional mixed case, an admissible index cannot create exactly one carry. -/
theorem exceptional_mixed_no_one_borrow
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∀ k, Admissible N m k → padicValNat p (N.choose k) ≠ 1 := by
  classical
  intro k hk hval
  letI : Fact p.Prime := ⟨hp⟩
  rcases hk with ⟨hkpos, hklt, hmk⟩
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hpmMod : p % m = m - 1 := by
    rw [hpm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpSucc : p + 1 = m := by omega
  obtain ⟨s, t, hst, hNpow, hopposite⟩ :=
    mixed_eq_sum_two_powers hm hp hpmMod hmN hmixed
  have hpowst : p ^ s < p ^ t :=
    Nat.pow_lt_pow_right hp1 hst
  have hpowle : p ^ t ≤ N := by
    rw [hNpow]
    omega
  have hNlt2 : N < 2 * p ^ t := by
    rw [hNpow]
    omega
  have hNltTop : N < p ^ (t + 1) := by
    calc
      N < 2 * p ^ t := hNlt2
      _ ≤ p * p ^ t := Nat.mul_le_mul_right (p ^ t) hp2
      _ = p ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
  have hlog : Nat.log p N = t :=
    Nat.log_eq_of_pow_le_of_lt_pow hpowle hNltTop
  have hkn : k ≤ N := hklt.le
  have hcount : carryCount p N k (t + 1) = 1 := by
    rw [← padicVal_choose_eq_carryCount
      (p := p) (n := N) (k := k) hkn (by rw [hlog]; omega)]
    exact hval
  rw [carryCount] at hcount
  obtain ⟨i, hfilter⟩ := Finset.card_eq_one.mp hcount
  have himem :
      i ∈ (Finset.Ico 1 (t + 1)).filter (fun j ↦ CarryAt p N k j) := by
    rw [hfilter]
    simp
  have hirange : i ∈ Finset.Ico 1 (t + 1) :=
    (Finset.mem_filter.mp himem).1
  have hiCarry : CarryAt p N k i :=
    (Finset.mem_filter.mp himem).2
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hirange).1
  have hit : i ≤ t := by
    have := (Finset.mem_Ico.mp hirange).2
    omega
  have hnocarry {j : ℕ} (hjt : j ≤ t) (hji : j ≠ i) :
      ¬ CarryAt p N k j := by
    by_cases hj0 : j = 0
    · subst j
      apply
        (not_carryAt_iff_mod_pow_le
          (p := p) (n := N) (k := k) (i := 0) hp0 hkn).2
      change k % 1 ≤ N % 1
      rw [Nat.mod_one, Nat.mod_one]
    · intro hjcarry
      have hjmem :
          j ∈ (Finset.Ico 1 (t + 1)).filter (fun r ↦ CarryAt p N k r) := by
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hj0, by omega⟩
        · exact hjcarry
      rw [hfilter] at hjmem
      have hjeq : j = i := by simpa using hjmem
      exact hji hjeq
  have hprefix_of_nocarry {j : ℕ} (hj : ¬ CarryAt p N k j) :
      k % p ^ j ≤ N % p ^ j :=
    (not_carryAt_iff_mod_pow_le
      (p := p) (n := N) (k := k) (i := j) hp0 hkn).1 hj
  have hprefix_gt_of_carry {j : ℕ} (hj : CarryAt p N k j) :
      N % p ^ j < k % p ^ j := by
    have hnotle : ¬ k % p ^ j ≤ N % p ^ j := by
      intro hle
      exact
        ((not_carryAt_iff_mod_pow_le
          (p := p) (n := N) (k := k) (i := j) hp0 hkn).2 hle) hj
    omega
  have hNmod_low {j : ℕ} (hjs : j ≤ s) :
      N % p ^ j = 0 := by
    rw [hNpow, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow p hjs),
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow p (hjs.trans hst.le))]
    simp
  have hNmod_mid {j : ℕ} (hsj : s < j) (hjt : j ≤ t) :
      N % p ^ j = p ^ s := by
    rw [hNpow, Nat.add_mod,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsj),
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow p hjt)]
    simpa using Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsj)
  have hkmod_mono (j : ℕ) :
      k % p ^ j ≤ k % p ^ (j + 1) := by
    rw [mod_pow_succ_eq_mod_add_digitAt]
    omega
  have hiloc : i = s ∨ i = t := by
    by_cases his : i = s
    · exact Or.inl his
    by_cases hit' : i = t
    · exact Or.inr hit'
    rcases lt_or_gt_of_ne his with hislt | hsilt
    · have hinext : ¬ CarryAt p N k (i + 1) :=
        hnocarry (by omega) (by omega)
      have hnext := hprefix_of_nocarry hinext
      have hcur := hprefix_gt_of_carry hiCarry
      have hNi : N % p ^ i = 0 :=
        hNmod_low (by omega)
      have hNnext : N % p ^ (i + 1) = 0 :=
        hNmod_low (by omega)
      have hkmono := hkmod_mono i
      rw [hNi] at hcur
      rw [hNnext] at hnext
      omega
    · have hilt : i < t := by omega
      have hinext : ¬ CarryAt p N k (i + 1) :=
        hnocarry (by omega) (by omega)
      have hnext := hprefix_of_nocarry hinext
      have hcur := hprefix_gt_of_carry hiCarry
      have hNi : N % p ^ i = p ^ s :=
        hNmod_mid hsilt hit
      have hNnext : N % p ^ (i + 1) = p ^ s :=
        hNmod_mid (by omega) (by omega)
      have hkmono := hkmod_mono i
      rw [hNi] at hcur
      rw [hNnext] at hnext
      omega
  rcases hiloc with his | hitop
  · subst i
    have hs1 : 1 ≤ s := hi1
    have hcur := hprefix_gt_of_carry hiCarry
    have hNs : N % p ^ s = 0 := hNmod_low le_rfl
    rw [hNs] at hcur
    have hkmods_pos : 0 < k % p ^ s := hcur
    have hprevnc : ¬ CarryAt p N k (s - 1) :=
      hnocarry (by omega) (by omega)
    have hprev := hprefix_of_nocarry hprevnc
    have hNprev : N % p ^ (s - 1) = 0 :=
      hNmod_low (by omega)
    rw [hNprev] at hprev
    have hkmodprev_zero : k % p ^ (s - 1) = 0 :=
      Nat.eq_zero_of_le_zero hprev
    let a := digitAt p k (s - 1)
    have hksform : k % p ^ s = p ^ (s - 1) * a := by
      have hrec := mod_pow_succ_eq_mod_add_digitAt p k (s - 1)
      have hsadd : s - 1 + 1 = s := Nat.sub_add_cancel hs1
      rw [hsadd, hkmodprev_zero] at hrec
      simpa [a] using hrec
    have ha0 : 0 < a := by
      by_contra hna
      have haeq : a = 0 := Nat.eq_zero_of_not_pos hna
      rw [haeq, mul_zero] at hksform
      omega
    have halt : a < p := by
      dsimp [a, digitAt]
      exact Nat.mod_lt _ hp0
    have htNc : ¬ CarryAt p N k t :=
      hnocarry le_rfl (by omega)
    have htPrefix := hprefix_of_nocarry htNc
    have hNt : N % p ^ t = p ^ s :=
      hNmod_mid hst le_rfl
    rw [hNt] at htPrefix
    have hkmodt_le : k % p ^ t ≤ p ^ s := htPrefix
    have hkmodt_lt : k % p ^ t < p ^ s := by
      by_contra hnot
      have heq : k % p ^ t = p ^ s := by omega
      have hnested :=
        Nat.mod_mod_of_dvd k (Nat.pow_dvd_pow p hst.le)
      rw [heq] at hnested
      simp at hnested
      omega
    have hkmodt_eq : k % p ^ t = k % p ^ s := by
      have hnested :=
        Nat.mod_mod_of_dvd k (Nat.pow_dvd_pow p hst.le)
      rw [Nat.mod_eq_of_lt hkmodt_lt] at hnested
      exact hnested
    let b := k / p ^ t
    have hb_lt : b < 2 := by
      dsimp [b]
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
      exact hklt.trans hNlt2
    have hb1 : b ≤ 1 := by omega
    have hkform : k = a * p ^ (s - 1) + b * p ^ t := by
      calc
        k = k % p ^ t + p ^ t * (k / p ^ t) :=
          (Nat.mod_add_div k (p ^ t)).symm
        _ = a * p ^ (s - 1) + b * p ^ t := by
          rw [hkmodt_eq, hksform]
          simp [b, Nat.mul_comm]
    have hsflip : Even (s - 1) ↔ ¬ Even s := by
      rw [Nat.even_sub' hs1, Nat.not_even_iff_odd]
      simp
    have hop : ¬ Even s ↔ Even t := by
      constructor
      · intro hsnot
        by_contra htnot
        apply hopposite
        exact
          ⟨fun hsE ↦ (hsnot hsE).elim,
            fun htE ↦ (htnot htE).elim⟩
      · intro htE hsE
        apply hopposite
        exact ⟨fun _ ↦ htE, fun _ ↦ hsE⟩
    have hpar : Even (s - 1) ↔ Even t :=
      hsflip.trans hop
    have habpos : 0 < a + b :=
      Nat.add_pos_left ha0 b
    have hablt : a + b < m := by
      rw [← hpSucc]
      omega
    have hbad :=
      not_dvd_add_same_parity_powers
        (m := m) (p := p) (a := a) (b := b)
        (u := s - 1) (v := t)
        hm hpmMod habpos hablt hpar
    apply hbad
    rw [← hkform]
    exact hmk
  · subst i
    have ht1 : 1 ≤ t := hi1
    have hsNc : ¬ CarryAt p N k s :=
      hnocarry hst.le (by omega)
    have hsPrefix := hprefix_of_nocarry hsNc
    have hNs : N % p ^ s = 0 := hNmod_low le_rfl
    rw [hNs] at hsPrefix
    have hkmods_zero : k % p ^ s = 0 :=
      Nat.eq_zero_of_le_zero hsPrefix
    have hprevNc : ¬ CarryAt p N k (t - 1) :=
      hnocarry (by omega) (by omega)
    have hprevPrefix := hprefix_of_nocarry hprevNc
    have hNprev_le : N % p ^ (t - 1) ≤ p ^ s := by
      by_cases hle : t - 1 ≤ s
      · rw [hNmod_low hle]
        omega
      · have hsltprev : s < t - 1 := Nat.lt_of_not_ge hle
        rw [hNmod_mid hsltprev (by omega)]
    have hkmodprev_le : k % p ^ (t - 1) ≤ p ^ s :=
      hprevPrefix.trans hNprev_le
    have hsleprev : s ≤ t - 1 := by omega
    have hkdvdps : p ^ s ∣ k :=
      Nat.dvd_of_mod_eq_zero hkmods_zero
    have hprevdvd : p ^ s ∣ k % p ^ (t - 1) :=
      (Nat.dvd_mod_iff (Nat.pow_dvd_pow p hsleprev)).2 hkdvdps
    let b := (k % p ^ (t - 1)) / p ^ s
    have hprevform : k % p ^ (t - 1) = b * p ^ s := by
      dsimp [b]
      exact (Nat.div_mul_cancel hprevdvd).symm
    have hbmul : b * p ^ s ≤ 1 * p ^ s := by
      rw [← hprevform]
      simpa using hkmodprev_le
    have hb1 : b ≤ 1 :=
      Nat.le_of_mul_le_mul_right hbmul (pow_pos hp0 s)
    have hcur := hprefix_gt_of_carry hiCarry
    have hNt : N % p ^ t = p ^ s :=
      hNmod_mid hst le_rfl
    rw [hNt] at hcur
    have hkmodt_gt : p ^ s < k % p ^ t := hcur
    let a := digitAt p k (t - 1)
    have halt : a < p := by
      dsimp [a, digitAt]
      exact Nat.mod_lt _ hp0
    have hktform :
        k % p ^ t =
          k % p ^ (t - 1) + p ^ (t - 1) * a := by
      have hrec := mod_pow_succ_eq_mod_add_digitAt p k (t - 1)
      have htadd : t - 1 + 1 = t := Nat.sub_add_cancel ht1
      rw [htadd] at hrec
      simpa [a] using hrec
    have ha0 : 0 < a := by
      by_contra hna
      have haeq : a = 0 := Nat.eq_zero_of_not_pos hna
      rw [haeq, mul_zero, add_zero] at hktform
      omega
    let q := k / p ^ t
    have hq_lt : q < 2 := by
      dsimp [q]
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp0 t)]
      exact hklt.trans hNlt2
    have hq1 : q ≤ 1 := by omega
    have hkdecomp :
        k = k % p ^ t + p ^ t * q := by
      simpa [q] using (Nat.mod_add_div k (p ^ t)).symm
    have hq0 : q = 0 := by
      by_contra hqne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
      have hqeq : q = 1 := by omega
      rw [hqeq, mul_one] at hkdecomp
      rw [hNpow] at hklt
      omega
    have hkform :
        k = b * p ^ s + a * p ^ (t - 1) := by
      calc
        k = k % p ^ t := by rw [hkdecomp, hq0]; simp
        _ = k % p ^ (t - 1) + p ^ (t - 1) * a := hktform
        _ = b * p ^ s + a * p ^ (t - 1) := by
          rw [hprevform]
          ac_rfl
    have htflip : Even (t - 1) ↔ ¬ Even t := by
      rw [Nat.even_sub' ht1, Nat.not_even_iff_odd]
      simp
    have hop : Even s ↔ ¬ Even t := by
      constructor
      · intro hsE htE
        apply hopposite
        exact ⟨fun _ ↦ htE, fun _ ↦ hsE⟩
      · intro htnot
        by_contra hsnot
        apply hopposite
        exact
          ⟨fun hsE ↦ (hsnot hsE).elim,
            fun htE ↦ (htnot htE).elim⟩
    have hpar : Even s ↔ Even (t - 1) :=
      hop.trans htflip.symm
    have hbapos : 0 < b + a :=
      Nat.add_pos_right b ha0
    have hbalt : b + a < m := by
      rw [← hpSucc]
      omega
    have hbad :=
      not_dvd_add_same_parity_powers
        (m := m) (p := p) (a := b) (b := a)
        (u := s) (v := t - 1)
        hm hpmMod hbapos hbalt hpar
    apply hbad
    rw [← hkform]
    exact hmk

/-- In the exceptional mixed case, the witness
`p^(t-1) + p^(t-2)` creates exactly the two carries at boundaries `t-1` and `t`. -/
theorem exceptional_mixed_two_borrow_witness
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 2 ≤ p := hp.two_le
  have hpmMod : p % m = m - 1 := by
    rw [hpm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpSucc : p + 1 = m := by omega
  obtain ⟨s, t, hst, hNpow, hopposite⟩ :=
    mixed_eq_sum_two_powers hm hp hpmMod hmN hmixed
  have ht2 : 2 ≤ t := by
    by_contra htNot
    have htlt : t < 2 := Nat.lt_of_not_ge htNot
    have hs0 : s = 0 := by omega
    have ht1 : t = 1 := by omega
    have hNeq : N = m := by
      rw [hNpow, hs0, ht1, pow_zero, pow_one]
      omega
    omega
  have hgap : s = t - 1 ∨ s < t - 2 := by
    by_cases hsPred : s = t - 1
    · exact Or.inl hsPred
    · right
      have hsne : s ≠ t - 2 := by
        intro hsEq
        apply hopposite
        have htEq : t = s + 2 := by omega
        rw [htEq, Nat.even_add']
        have hnotOddTwo : ¬ Odd (2 : ℕ) := by
          norm_num [Odd]
        simp [hnotOddTwo, Nat.not_odd_iff_even]
      omega
  have hpowst : p ^ s < p ^ t :=
    Nat.pow_lt_pow_right hp1 hst
  have hpowle : p ^ t ≤ N := by
    rw [hNpow]
    omega
  have hNlt2 : N < 2 * p ^ t := by
    rw [hNpow]
    omega
  have hNltTop : N < p ^ (t + 1) := by
    calc
      N < 2 * p ^ t := hNlt2
      _ ≤ p * p ^ t := Nat.mul_le_mul_right (p ^ t) hp2
      _ = p ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
  have hlog : Nat.log p N = t :=
    Nat.log_eq_of_pow_le_of_lt_pow hpowle hNltTop
  have hpowPred :
      p ^ (t - 2) < p ^ (t - 1) :=
    Nat.pow_lt_pow_right hp1 (by omega)
  let k := p ^ (t - 1) + p ^ (t - 2)
  have hkpos : 0 < k := by
    dsimp [k]
    positivity
  have hkltpow : k < p ^ t := by
    have hlt2 :
        p ^ (t - 1) + p ^ (t - 2) < 2 * p ^ (t - 1) := by
      omega
    dsimp [k]
    calc
      p ^ (t - 1) + p ^ (t - 2) < 2 * p ^ (t - 1) := hlt2
      _ ≤ p * p ^ (t - 1) := Nat.mul_le_mul_right (p ^ (t - 1)) hp2
      _ = p ^ (t - 1) * p := Nat.mul_comm _ _
      _ = p ^ ((t - 1) + 1) := (pow_succ p (t - 1)).symm
      _ = p ^ t := by rw [Nat.sub_add_cancel (by omega)]
  have hkN : k < N := hkltpow.trans_le hpowle
  have hkn : k ≤ N := hkN.le
  have hmk : m ∣ k := by
    refine ⟨p ^ (t - 2), ?_⟩
    dsimp [k]
    have htSub : t - 2 + 1 = t - 1 := by omega
    calc
      p ^ (t - 1) + p ^ (t - 2) =
          p ^ (t - 2) * p + p ^ (t - 2) := by
            rw [← pow_succ, htSub]
      _ = (p + 1) * p ^ (t - 2) := by ring
      _ = m * p ^ (t - 2) := by rw [hpSucc]
  have hnocarry_of_lt {j : ℕ} (hjt : j < t - 1) :
      ¬ CarryAt p N k j := by
    apply
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := j) hp0 hkn).2
    have hj2 : j ≤ t - 2 := by omega
    have hj1 : j ≤ t - 1 := by omega
    have hdvd : p ^ j ∣ k := by
      dsimp [k]
      exact dvd_add
        (Nat.pow_dvd_pow p hj1)
        (Nat.pow_dvd_pow p hj2)
    rw [Nat.mod_eq_zero_of_dvd hdvd]
    exact Nat.zero_le _
  have hkmodPred : k % p ^ (t - 1) = p ^ (t - 2) := by
    dsimp [k]
    rw [Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt hpowPred]
    simpa using Nat.mod_eq_of_lt hpowPred
  have hNmodPredLt : N % p ^ (t - 1) < p ^ (t - 2) := by
    rcases hgap with hsPred | hsLow
    · have htopdvd : p ^ (t - 1) ∣ p ^ t :=
        Nat.pow_dvd_pow p (by omega)
      rw [hNpow, hsPred, Nat.add_mod, Nat.mod_self,
        Nat.mod_eq_zero_of_dvd htopdvd]
      simpa using pow_pos hp0 (t - 2)
    · have hsPredLt : s < t - 1 := by omega
      have hsPowLt : p ^ s < p ^ (t - 2) :=
        Nat.pow_lt_pow_right hp1 hsLow
      have htopdvd : p ^ (t - 1) ∣ p ^ t :=
        Nat.pow_dvd_pow p (by omega)
      rw [hNpow, Nat.add_mod,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsPredLt),
        Nat.mod_eq_zero_of_dvd htopdvd]
      simpa [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right hp1 hsPredLt)] using hsPowLt
  have hcarryPred : CarryAt p N k (t - 1) := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t - 1) hp0 hkn).1 hnocarry
    rw [hkmodPred] at hprefix
    omega
  have hNmodTop : N % p ^ t = p ^ s := by
    rw [hNpow, Nat.add_mod, Nat.mod_eq_of_lt hpowst, Nat.mod_self]
    simpa using Nat.mod_eq_of_lt hpowst
  have hpowSltK : p ^ s < k := by
    dsimp [k]
    by_cases hsPred : s = t - 1
    · rw [hsPred]
      have hpowLowPos : 0 < p ^ (t - 2) := pow_pos hp0 _
      omega
    · have hsLow : s < t - 1 := by omega
      have hpowLow : p ^ s < p ^ (t - 1) :=
        Nat.pow_lt_pow_right hp1 hsLow
      omega
  have hcarryTop : CarryAt p N k t := by
    by_contra hnocarry
    have hprefix :=
      (not_carryAt_iff_mod_pow_le
        (p := p) (n := N) (k := k) (i := t) hp0 hkn).1 hnocarry
    rw [Nat.mod_eq_of_lt hkltpow, hNmodTop] at hprefix
    exact (Nat.not_le_of_gt hpowSltK) hprefix
  have hfilter :
      ((Finset.Ico 1 (t + 1)).filter fun i ↦ CarryAt p N k i) =
        {t - 1, t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hj1, hjlt⟩, hjcarry⟩
      by_cases hjTop : j = t
      · exact Or.inr hjTop
      by_cases hjPred : j = t - 1
      · exact Or.inl hjPred
      have hjltPred : j < t - 1 := by omega
      exact (hnocarry_of_lt hjltPred hjcarry).elim
    · intro hj
      rcases hj with hjPred | hjTop
      · subst j
        exact ⟨⟨by omega, by omega⟩, hcarryPred⟩
      · subst j
        exact ⟨⟨by omega, Nat.lt_succ_self t⟩, hcarryTop⟩
  have hcount : carryCount p N k (t + 1) = 2 := by
    rw [carryCount, hfilter]
    have hne : t - 1 ≠ t := by omega
    simp [hne]
  have hloglt : Nat.log p N < t + 1 := by
    rw [hlog]
    exact Nat.lt_succ_self t
  have hval : padicValNat p (N.choose k) = 2 := by
    rw [padicVal_choose_eq_carryCount hkn hloglt, hcount]
  exact ⟨k, ⟨hkpos, hkN, hmk⟩, hval⟩

/-- Main target theorem for primes congruent to `-1` modulo `m`. -/
theorem minus_one_valuation
    {m N p : ℕ}
    (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) := by
  have hm0 : 0 < m := by omega
  have hNne : N ≠ 0 := by omega
  have hdigitsNe : Nat.digits p N ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr hNne
  have hsumpos : 0 < (Nat.digits p N).sum :=
    List.sum_pos_iff_exists_pos_nat.mpr
      ⟨(Nat.digits p N).getLast hdigitsNe, List.getLast_mem hdigitsNe,
        Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hNne)⟩
  have hABpos :
      0 < evenDigitSum p N + oddDigitSum p N := by
    simpa [evenDigitSum, oddDigitSum, parityDigitSums_add_eq_sum] using hsumpos
  have hzero :
      SignedZeroSum m (evenDigitSum p N) (oddDigitSum p N) :=
    (dvd_iff_signedZeroSum_digitSums
      (m := m) (p := p) (k := N) (by omega) hpm).1 hmN
  have hpCase : p = m - 1 ∨ m < p := by
    by_cases hedge : p = m - 1
    · exact Or.inl hedge
    · right
      by_contra hnot
      have hple : p ≤ m := Nat.le_of_not_gt hnot
      by_cases hlt : p < m
      · have hpmod : p % m = p := Nat.mod_eq_of_lt hlt
        apply hedge
        omega
      · have hpeq : p = m := by omega
        subst p
        rw [Nat.mod_self] at hpm
        omega
  by_cases hproper :
      HasProperZeroSubmultiset m (evenDigitSum p N) (oddDigitSum p N)
  · have hwit0 :
        ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 0 :=
      (noBorrow_iff_proper_signed_zero_sum hm hp hpm hmN).2 hproper
    have hG0 : padicValNat p (G N m) = 0 :=
      padicVal_G_eq_of_lower_bound_of_witness
        hm0 hNm hp (fun _ _ ↦ Nat.zero_le _) hwit0
    have hnotminimal :
        ¬ MinimalSignedZeroSum m (evenDigitSum p N) (oddDigitSum p N) := by
      intro hminimal
      exact hminimal.2.2 hproper
    have hnotshapes :
        ¬ ((evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) ∨
          (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) := by
      intro hshapes
      exact hnotminimal
        ((minimal_signed_zero_sum_classification hm).2 hshapes)
    have hnotMixed :
        ¬ (evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) := by
      intro hmix
      exact hnotshapes (Or.inl hmix)
    have hnotUniform :
        ¬ ((evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) := by
      intro hunif
      exact hnotshapes (Or.inr hunif)
    have hnotFirst :
        ¬ (evenDigitSum p N = 1 ∧ oddDigitSum p N = 1 ∧ p = m - 1) := by
      rintro ⟨heven, hodd, _⟩
      exact hnotMixed ⟨heven, hodd⟩
    have hnotSecond :
        ¬ (evenDigitSum p N = 1 ∧ oddDigitSum p N = 1 ∧ m < p) := by
      rintro ⟨heven, hodd, _⟩
      exact hnotMixed ⟨heven, hodd⟩
    simpa [minusOneExpectedValuation, hnotFirst, hnotSecond, hnotUniform] using hG0
  · have hminimal :
        MinimalSignedZeroSum m (evenDigitSum p N) (oddDigitSum p N) :=
      ⟨hABpos, hzero, hproper⟩
    have hpositive :
        ∀ k, Admissible N m k → 1 ≤ padicValNat p (N.choose k) := by
      intro k hkadm
      have hne : padicValNat p (N.choose k) ≠ 0 := by
        intro hval0
        apply hproper
        exact
          (noBorrow_iff_proper_signed_zero_sum hm hp hpm hmN).1
            ⟨k, hkadm, hval0⟩
      omega
    rcases (minimal_signed_zero_sum_classification hm).1 hminimal with
      hmixed | huniformLeft | huniformRight
    · rcases hmixed with ⟨heven, hodd⟩
      have hmixed' :
          evenDigitSum p N = 1 ∧ oddDigitSum p N = 1 :=
        ⟨heven, hodd⟩
      rcases hpCase with hedge | hgt
      · have hnoOne :
            ∀ k, Admissible N m k → padicValNat p (N.choose k) ≠ 1 :=
          exceptional_mixed_no_one_borrow hm hp hedge hmN hNm hmixed'
        have hlower2 :
            ∀ k, Admissible N m k → 2 ≤ padicValNat p (N.choose k) := by
          intro k hkadm
          have hpos := hpositive k hkadm
          have hne1 := hnoOne k hkadm
          omega
        have hwit2 :
            ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 2 :=
          exceptional_mixed_two_borrow_witness hm hp hedge hmN hNm hmixed'
        have hG2 : padicValNat p (G N m) = 2 :=
          padicVal_G_eq_of_lower_bound_of_witness
            hm0 hNm hp hlower2 hwit2
        have hexpected :
            minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) = 2 := by
          rw [minusOneExpectedValuation, if_pos ⟨heven, hodd, hedge⟩]
        exact hG2.trans hexpected.symm
      · have hwit1 :
            ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 :=
          mixed_case_one_borrow_of_gt hm hp hpm hgt hmixed'
        have hG1 : padicValNat p (G N m) = 1 :=
          padicVal_G_eq_of_lower_bound_of_witness
            hm0 hNm hp hpositive hwit1
        have hneEdge : p ≠ m - 1 := by omega
        simpa [minusOneExpectedValuation, heven, hodd, hgt, hneEdge] using hG1
    · rcases huniformLeft with ⟨heven, hodd⟩
      have huniform :
          (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m) :=
        Or.inl ⟨heven, hodd⟩
      have hwit1 :
          ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
        rcases hpCase with hedge | hgt
        · rcases uniform_case_one_borrow_edge hm hp hedge hmN hNm huniform with
            ⟨t, s, k, hst, htocc, hsocc, hkdef, hkadm, hval⟩
          exact ⟨k, hkadm, hval⟩
        · exact uniform_case_one_borrow_of_gt hm hp hpm hgt hmN hNm huniform
      have hG1 : padicValNat p (G N m) = 1 :=
        padicVal_G_eq_of_lower_bound_of_witness
          hm0 hNm hp hpositive hwit1
      simpa [minusOneExpectedValuation, heven, hodd] using hG1
    · rcases huniformRight with ⟨heven, hodd⟩
      have huniform :
          (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
          (evenDigitSum p N = 0 ∧ oddDigitSum p N = m) :=
        Or.inr ⟨heven, hodd⟩
      have hwit1 :
          ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by
        rcases hpCase with hedge | hgt
        · rcases uniform_case_one_borrow_edge hm hp hedge hmN hNm huniform with
            ⟨t, s, k, hst, htocc, hsocc, hkdef, hkadm, hval⟩
          exact ⟨k, hkadm, hval⟩
        · exact uniform_case_one_borrow_of_gt hm hp hpm hgt hmN hNm huniform
      have hG1 : padicValNat p (G N m) = 1 :=
        padicVal_G_eq_of_lower_bound_of_witness
          hm0 hNm hp hpositive hwit1
      simpa [minusOneExpectedValuation, heven, hodd] using hG1

end PascalMinusOne
