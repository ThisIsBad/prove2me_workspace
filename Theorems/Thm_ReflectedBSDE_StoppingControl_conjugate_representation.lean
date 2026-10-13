import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- §7, p. 724 (conjugacy display). If `f(ω, t, ·, ·)` is concave on `ℝ × ℝ^d` for each
`(ω, t)` and `f` satisfies the Lipschitz condition (iii), then for each `(ω, t)` and `(y, z)`,
`f(t, y, z) = inf_{(β, γ) ∈ D^F_t} {F(t, β, γ) + βy + ⟨γ, z⟩}` with the infimum achieved, and
a.s. the set `D^F_t` is bounded (for every `t ∈ [0, T]`). -/
theorem conjugate_representation {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K) :
    (∀ ω, ∀ t ≤ T, ∀ (y : ℝ) (z : Fin d → ℝ),
      (∀ p ∈ conjDomain f ω t, f t ω y z ≤ (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
      ∃ p ∈ conjDomain f ω t, f t ω y z = (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
    ∀ᵐ ω ∂P, ∀ t ≤ T, Bornology.IsBounded (conjDomain f ω t) := by sorry

end ReflectedBSDE.StoppingControl

