import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Proof of Theorem (4.4), p. 28** (unnumbered): "It is clear that
`Z_1 + ⋯ Z_n = Y_1^n + ⋯ + Y_n^n`" (the page omits a `+`). Pathwise, for every real
sequence and every `n`. -/
theorem proof_4_4_regroup {Ω : Type*} (σ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ m ∈ Finset.Icc 1 n, Z σ m ω = ∑ k ∈ Finset.Icc 1 n, Y σ k n ω := by sorry

end SolomonRWRE.DiffEq

