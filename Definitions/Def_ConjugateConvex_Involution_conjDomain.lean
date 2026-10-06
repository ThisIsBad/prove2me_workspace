import Mathlib

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75: `Γ` is the set of all points `ξ` such that `Σxξ − f(x)` is
bounded from above in `G`. -/
def conjDomain {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {ξ | BddAbove ((fun x => x ⬝ᵥ ξ - f x) '' G)}

end ConjugateConvex.Involution
