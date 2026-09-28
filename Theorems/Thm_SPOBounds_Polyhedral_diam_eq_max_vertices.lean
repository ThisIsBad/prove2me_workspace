import Mathlib

namespace SPOBounds.Polyhedral

/-- arXiv:1905.11488v3, §5.2, p. 25, the sentence before Theorem 8: for `S = conv{v_1, …, v_K}`
(distinct `v_i`, `K ≥ 1`), the diameter `Δ(S) = sup_{w₁, w₂ ∈ S} ‖w₁ − w₂‖` equals
`max_{i, j} ‖v_i − v_j‖`. -/
theorem diam_eq_max_vertices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℕ} (hK : 0 < K) (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) :
    IsGreatest (Set.range fun p : Fin K × Fin K => ‖v p.1 - v p.2‖) (Metric.diam S) := by sorry

end SPOBounds.Polyhedral
