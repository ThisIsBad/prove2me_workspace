import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology

namespace ArmijoGrad.Conv

/-- THEOREM (§2), pp. 1–2. If `0 < δ ≤ 1/4K`, then for any `x ∈ S(x₀)` the set `S*(x, δ)` of (1)
is a nonempty subset of `S(x₀)`, and any sequence with `x₀` as first term and
`x_{k+1} ∈ S*(x_k, δ)` converges to the minimizer `x*`. -/
theorem convergence_theorem {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (K : ℝ)
    (hIII : ConditionIII f x0 K) (xstar : EuclideanSpace ℝ (Fin n))
    (hIV : ConditionIV f x0 xstar) (δ : ℝ) (hδ : 0 < δ) (hδK : δ ≤ 1 / (4 * K)) :
    (∀ x ∈ levelSet f x0, (sdSet f x δ).Nonempty ∧ sdSet f x δ ⊆ levelSet f x0) ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → (∀ k, x (k + 1) ∈ sdSet f (x k) δ) →
        Tendsto x atTop (𝓝 xstar) := by sorry

end ArmijoGrad.Conv

