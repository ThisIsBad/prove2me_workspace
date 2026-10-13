import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StochApproxDyn.SubgaussianNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.4, p. 17: maximal tail bound in a fixed direction.
For a Robbins–Monro algorithm with subgaussian noise (constant `Γ`), every unit vector `e`,
every `α > 0`, every `n` and every `T > 0`,
`P(sup_{n < k ≤ m(τ_n+T)} ⟨e, ∑_{i=n}^{k-1} γ_{i+1} U_{i+1}⟩ ≥ α)
  ≤ exp(−α² / (2Γ ∑_{i=n}^{m(τ_n+T)-1} γ_{i+1}²))`.
The supremum over the finite range of `k` is at least `α` iff some term is; the event is
written that way (an empty range gives the empty event). When the block sum of `γ²` vanishes,
Lean's `x / 0 = 0` makes the right side `1`, so the bound is then trivially true (and the left
side is `0` anyway). The paper states it for `e ∈ {±e_1, …, ±e_d}`; every unit vector is
allowed here. -/
theorem directional_maximal_tail {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (Γ : ℝ) (hΓ : 0 < Γ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) (α : ℝ) (hα : 0 < α)
    (n : ℕ) (T : ℝ) (hT : 0 < T) :
    P {ω | ∃ k ∈ Finset.Ioc n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
        α ≤ ⟪e, ∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω⟫_ℝ}
      ≤ ENNReal.ofReal (Real.exp (-α ^ 2 /
          (2 * Γ * ∑ i ∈ Finset.Ico n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)), γ (i + 1) ^ 2))) := by sorry

end StochApproxDyn.SubgaussianNoise

