import Mathlib.Data.Nat.Digits.Lemmas

namespace PascalMinusOne

/-- Alternating sums of a little-endian digit list: even positions, then odd positions. -/
def parityDigitSums : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | d :: ds =>
      let tail := parityDigitSums ds
      (d + tail.2, tail.1)

/-- Sum of base-`p` digits of `N` in even exponent positions. -/
def evenDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).1

/-- Sum of base-`p` digits of `N` in odd exponent positions. -/
def oddDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).2

/-- Arithmetic digit accessor, useful when list indexing is inconvenient. -/
def digitAt (p N i : ℕ) : ℕ :=
  N / p ^ i % p

/-- An exponent is occupied when its base-`p` digit is positive. -/
def Occupied (p N i : ℕ) : Prop :=
  0 < digitAt p N i

@[simp] theorem parityDigitSums_nil : parityDigitSums [] = (0, 0) := rfl

@[simp] theorem parityDigitSums_cons (d : ℕ) (ds : List ℕ) :
    parityDigitSums (d :: ds) =
      (d + (parityDigitSums ds).2, (parityDigitSums ds).1) := rfl

@[simp] theorem evenDigitSum_zero (p : ℕ) : evenDigitSum p 0 = 0 := by
  simp [evenDigitSum]

@[simp] theorem oddDigitSum_zero (p : ℕ) : oddDigitSum p 0 = 0 := by
  simp [oddDigitSum]

end PascalMinusOne
