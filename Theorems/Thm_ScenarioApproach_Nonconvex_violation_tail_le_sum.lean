import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_violation
import Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram
import Definitions.Def_ScenarioApproach_Nonconvex_supportSet

namespace ScenarioApproach.Nonconvex

/-- Eq. (8.15) (proven in [31], Campi–Garatti–Ramponi 2018). Nonconvex scenario program (8.12)
over a generic set `Θ` with cost `f` and constraints `Θδ`. `θstar ω` is the solution with the
`N` sampled constraints `ω`, and `alg` is any algorithm returning a support set
(Definition 8.8) `alg ω` for every sample; `σ* = (alg ω).card`. For every
`ε : {0, …, N} → [0, 1]` with `ε(N) = 1`,
`ℙ^N{V(θ*) > ε(σ*)} ≤ ∑_{k=0}^{N−1} (N choose k) (1 − ε(k))^{N−k}`. -/
theorem violation_tail_le_sum {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (f : Θ → ℝ) (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (hθstar_meas : Measurable θstar)
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω))
    (halg_meas : ∀ J : Finset (Fin N), MeasurableSet {ω | alg ω = J})
    (ε : ℕ → ℝ) (hε : ∀ k ≤ N, ε k ∈ Set.Icc (0 : ℝ) 1) (hεN : ε N = 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | ε (alg ω).card < violation P Θδ (θstar ω)} ≤
      ENNReal.ofReal (∑ k ∈ Finset.range N, (N.choose k : ℝ) * (1 - ε k) ^ (N - k)) := by sorry

end ScenarioApproach.Nonconvex

