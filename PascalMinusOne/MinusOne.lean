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

/-- A little-endian natural digit list with total digit mass one is bounded by
its highest available place value. -/
lemma ofDigits_le_pow_length_pred_of_sum_eq_one {p : ℕ} :
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
        have hlen : 1 ≤ ds.length := by
          exact List.length_pos_iff_ne_nil.mpr hdsne
        have hih := ih htail
        simp only [Nat.ofDigits_cons, zero_add, List.length_cons]
        calc
          p * Nat.ofDigits p ds ≤ p * p ^ (ds.length - 1) :=
            Nat.mul_le_mul_left p hih
          _ = p ^ (ds.length - 1) * p := by
            rw [Nat.mul_comm]
          _ = p ^ ((ds.length - 1) + 1) := (pow_succ p (ds.length - 1)).symm
          _ = p ^ ds.length := by rw [Nat.sub_add_cancel hlen]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        have hd1 : d = 1 := by omega
        have htail : ds.sum = 0 := by omega
        have hofd : Nat.ofDigits p ds = 0 := by
          induction ds with
          | nil => simp
          | cons e es ih0 =>
              simp only [List.sum_cons] at htail
              have he : e = 0 := by omega
              have hes : es.sum = 0 := by omega
              subst e
              simp [Nat.ofDigits_cons, ih0 hes]
        subst d
        simp [Nat.ofDigits_cons, hofd]

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
      ofDigits_le_pow_length_pred_of_sum_eq_one (p := p) (L.take t) hprefsum
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
