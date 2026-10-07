import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

/-- Inequality (6.8) (Bubeck, arXiv:1405.4980v2, proof of Theorem 6.11, p. 346):
`1 − (2/π) arcsin(t) ≥ 0.878 (1 − t)` for all `t ∈ [−1, 1]`. -/
theorem eq_6_8 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    1 - 2 / Real.pi * Real.arcsin t ≥ (0.878 : ℝ) * (1 - t) := by sorry

end ConvexOptAlg.GoemansWilliamson

