import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
import Definitions.Def_ScenarioApproach_EmpiricalCosts_supportConstraint

namespace ScenarioApproach.EmpiricalCosts

/-- p. 90: for fully supported problems (Definition 5.4), `ℓ* = ℓ*_d` with probability 1, where
`ℓ* = max_i ℓ(ν*, δᵢ)` is the optimal value of the scenario program (1.4) with `ν ∈ ℝ^n`,
`d = n + 1`, and `ℓ*_d` is its `d`-th empirical cost. -/
theorem worstCost_eq_empiricalCost_d_of_fullySupported
    {n N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    -- standing assumption (p. 6): `ℓ(ν, δ)` is convex in `ν` for every `δ`
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ)
    -- measurability, glossed over in the book (p. 6, footnote 1; p. 33)
    (hmeas : Measurable (Function.uncurry ℓ))
    -- Assumption 3.6 for (1.4): existence and uniqueness for every `m ≥ 1` and every sample
    (hexu : ∀ m : ℕ, 1 ≤ m → ∀ ω : Fin m → Δ, ∃! ν, IsSolution ℓ ω ν)
    -- Definition 5.4 for (1.4)
    (hfs : FullySupported P ℓ)
    -- `νstar ω` is the solution `ν*` of the scenario program with the `N` scenarios `ω`
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω)) (hνstar_meas : Measurable νstar)
    (hN : n + 1 ≤ N) :
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin N => P),
      worstCost ℓ ω (νstar ω) = empiricalCost ℓ ω (νstar ω) (n + 1) := by sorry

end ScenarioApproach.EmpiricalCosts

