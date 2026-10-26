import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic

namespace PrescAnalytics.ERM

open MeasureTheory

/-- Theorem 13 (p. 39), with the corrected hypotheses `0 ≤ c ≤ c̄` and `δ' = δ'' = δ` (i.i.d. case of
Theorem 21). Let `μ` be a probability measure on `𝒳 × 𝒴`, `F` a pointwise separable class of
measurable decision rules `𝒳 → ℝ^d`, `c(z; y)` a jointly measurable cost with values in `[0, c̄]` that
is `L`-Lipschitz in `z` for the `∞`-norm, uniformly in `y`; `N ≥ 1`, `δ > 0`. Then, for i.i.d.
samples `S_N ∼ μ^N`, each of the following fails, for some `z ∈ F`, only on a set of outer measure
at most `δ`:
(26) `E[c(z(X); Y)] ≤ (1/N) Σ_i c(z(x^i); y^i) + c̄ √(log(1/δ)/(2N)) + L ℜ_N(F)` for all `z ∈ F`,
(27) `E[c(z(X); Y)] ≤ (1/N) Σ_i c(z(x^i); y^i) + 3c̄ √(log(2/δ)/(2N)) + L ℜ̂_N(F; S_N^x)` for all
`z ∈ F`, where `ℜ_N(F)` is taken over i.i.d. covariate samples from the marginal `μ_X`. -/
theorem theorem_13_out_of_sample {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ]
    (F : Set (X → Fin d → ℝ)) (hF_meas : ∀ f ∈ F, Measurable f) (hF_sep : IsPointwiseSeparable F)
    (c : (Fin d → ℝ) → Y → ℝ) (hc_meas : Measurable (Function.uncurry c))
    (cbar L : ℝ) (hc_bdd : ∀ (z : Fin d → ℝ) (y : Y), 0 ≤ c z y ∧ c z y ≤ cbar)
    (hL : 0 ≤ L) (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F <
          ENNReal.ofReal (expCost μ c f - empCost s c f
            - cbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} ≤ ENNReal.ofReal δ ∧
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, (L : EReal) * empRademacher F (fun i => (s i).1) <
          ((expCost μ c f - empCost s c f
            - 3 * cbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by sorry

end PrescAnalytics.ERM

