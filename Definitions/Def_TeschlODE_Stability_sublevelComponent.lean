import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.6, p. 201: `S_δ`, the connected component of `{x ∈ U | L(x) ≤ δ}` containing
`x₀` (empty when `x₀` is not in that set, e.g. for `δ < L x₀`). -/
def sublevelComponent {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (L : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  connectedComponentIn {x | x ∈ U ∧ L x ≤ δ} x₀

end TeschlODE.Stability
