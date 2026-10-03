import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.337 (the "nondecreasing" hypothesis of Theorem
11.13): monotonicity of a utility-type function, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- `U : Zᴷ → R ∪ {−∞}` is nondecreasing: `x ≤ y` pointwise implies `U(x) ≤ U(y)`. -/
def Nondecreasing {K : Type*} (U : (K → ℤ) → WithBot ℝ) : Prop :=
  ∀ x y : K → ℤ, (∀ k, x k ≤ y k) → U x ≤ U y

end DiscreteConvex.EconomicEquilibrium
