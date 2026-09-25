import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Pascal Minus-One GCD: advertised statement

This is the small Palomar-facing statement surface for the project's principal
result. It imports only Mathlib. The definitions below are ordinary mathematical
definitions and are themselves compared against the corresponding Solution
definitions, so the theorem cannot be weakened by changing a helper definition.

For natural numbers `N,m`, `G N m` is the gcd of `N.choose k` over positive
multiples of `m` with `k < N`. For a base `p`, `evenDigitSum p N` and
`oddDigitSum p N` are the sums of the little-endian base-`p` digits in even
and odd exponent positions respectively.
-/

namespace PascalMinusOnePalomar

/-- The restricted gcd of binomial coefficients at positive multiples of `m` below `N`. -/
def G (N m : ℕ) : ℕ :=
  ((Finset.range N).filter fun k ↦ 0 < k ∧ m ∣ k).gcd fun k ↦ N.choose k

/-- Split a little-endian digit list into the sums in even and odd positions. -/
def parityDigitSums : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | d :: ds =>
      let tail := parityDigitSums ds
      (d + tail.2, tail.1)

/-- Sum of the base-`p` digits of `N` in even exponent positions. -/
def evenDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).1

/-- Sum of the base-`p` digits of `N` in odd exponent positions. -/
def oddDigitSum (p N : ℕ) : ℕ :=
  (parityDigitSums (Nat.digits p N)).2

/-- The piecewise valuation appearing in the minus-one theorem. -/
def minusOneExpectedValuation (m p A B : ℕ) : ℕ :=
  if A = 1 ∧ B = 1 ∧ p = m - 1 then 2
  else if A = 1 ∧ B = 1 ∧ m < p then 1
  else if (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) then 1
  else 0

/--
Let `m ≥ 3`, let `m ∣ N` with `m < N`, and let `p` be prime with
`p ≡ -1 (mod m)`, expressed as `p % m = m - 1`. If `A` and `B` are the
sums of the base-`p` digits of `N` in even and odd exponent positions, then
the `p`-adic valuation of the restricted gcd is:

* 2 when `(A,B) = (1,1)` and `p = m - 1`;
* 1 when `(A,B) = (1,1)` and `m < p`;
* 1 when `(A,B) = (m,0)` or `(0,m)`;
* 0 otherwise.
-/
theorem minus_one_valuation
    {m N p : ℕ}
    (hm : 3 ≤ m) (hmN : m ∣ N) (hNm : m < N)
    (hp : p.Prime) (hpm : p % m = m - 1) :
    padicValNat p (G N m) =
      minusOneExpectedValuation m p (evenDigitSum p N) (oddDigitSum p N) := by
  sorry

end PascalMinusOnePalomar
