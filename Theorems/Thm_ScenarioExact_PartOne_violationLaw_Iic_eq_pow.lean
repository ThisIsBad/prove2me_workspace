import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint
import Definitions.Def_ScenarioExact_PartOne_Basic
open MeasureTheory ScenarioApproach.Generalization
open scoped ENNReal

namespace ScenarioExact.PartOne

/-- (3.2), p. 7: for a fully-supported problem the distribution of the violation of `x*_d`
is `F(α) = α^d` on `[0, 1]`. -/
theorem violationLaw_Iic_eq_pow
    {d : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    -- Assumption 1 / (1.1): `𝒳` and every `𝒳_δ` are convex and closed
    (hΘ_convex : Convex ℝ Θ) (hΘ_closed : IsClosed Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ)) (hΘδ_closed : ∀ δ, IsClosed (Θδ δ))
    -- Assumption 1: for every number `k` of constraints and every sample, `P_k` has a unique solution
    (hexu : ∀ (k : ℕ) (ω : Fin k → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    -- measurability ("assumed for granted", p. 4): the constraint relation is jointly measurable
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    -- `θs k ω` is the solution `x*_k` of `P_k` with the sampled constraints `ω`; measurable in `ω`
    (θs : (k : ℕ) → (Fin k → Δ) → EuclideanSpace ℝ (Fin d))
    (hθs : ∀ (k : ℕ) (ω : Fin k → Δ), IsSolution c Θ Θδ ω (θs k ω))
    (hθs_meas : ∀ k, Measurable (θs k))
    -- Definition 2.3: the problem is fully-supported
    (hfs : FullySupported c Θ Θδ P)
    (hd : 1 ≤ d) :
    ∀ α ∈ Set.Icc (0 : ℝ) 1, violationLaw P Θδ θs (Set.Iic α) = ENNReal.ofReal (α ^ d) := by sorry

end ScenarioExact.PartOne

