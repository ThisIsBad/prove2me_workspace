import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology

namespace ArmijoGrad.Conv

/-- §2, proof of the THEOREM, p. 2: if `f` is bounded below, `x₀` is the first term and
`x_{k+1} ∈ S*(x_k, δ)` for every `k`, then `|∇f(x_k)| → 0`. -/
theorem gradient_norm_tendsto_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 < δ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx0 : x 0 = x0)
    (hseq : ∀ k, x (k + 1) ∈ sdSet f (x k) δ) :
    Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0) := by sorry

end ArmijoGrad.Conv

