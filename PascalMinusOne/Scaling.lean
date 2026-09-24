import PascalMinusOne.Basic

namespace PascalMinusOne

/-- TODO(Scaling-1): removing common trailing base-`p` zeros preserves the restricted-gcd valuation. -/
theorem scaling_valuation
    {p c q N' : ℕ} (hp : p.Prime) :
    padicValNat p (G (p ^ c * N') (p ^ c * q)) = padicValNat p (G N' q) := by
  sorry

end PascalMinusOne
