import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

/-- Lemma 2 (p. 846), sign-corrected. For the linear recursion (A8)
`Δ_t = Δ_{t-1} - γ_t (A Δ_{t-1} + ξ_t)` driven by an arbitrary sequence `ξ_1, ξ_2, … ∈ ℝ^N`
from an arbitrary `Δ_0`, with `Δ̄_t = (1/t) ∑_{i=0}^{t-1} Δ_i`, `α_t = α_0^t` and
`w_j^t = α_j^t - A⁻¹`: for every `t ≥ 1`,
`√t Δ̄_t = (1/(√t γ_0)) α_t Δ_0 - (1/√t) ∑_{j=1}^{t-1} A⁻¹ ξ_j - (1/√t) ∑_{j=1}^{t-1} w_j^t ξ_j`;
and under the hypotheses of Lemma 1 there is `K` with `‖α_t‖ ≤ K`, `‖w_j^t‖ ≤ K` for
`1 ≤ j < t`, and `(1/t) ∑_{j=1}^{t-1} ‖w_j^t‖ → 0`. -/
theorem lemma2_representation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (hA : EigenRePos A) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ)
    (Δ₀ : EuclideanSpace ℝ (Fin N)) (ξ : ℕ → EuclideanSpace ℝ (Fin N)) :
    (∀ t : ℕ, 1 ≤ t →
      Real.sqrt t • detAverage Δ₀ γ (matApply A) ξ t =
        (Real.sqrt t * γ 0)⁻¹ • matApply (lemAlpha A γ 0 t) Δ₀
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply A⁻¹ (ξ j)
          - (Real.sqrt t)⁻¹ • ∑ j ∈ Finset.Ico 1 t, matApply (lemW A γ j t) (ξ j)) ∧
    ∃ K : ℝ, (∀ t, matNorm (lemAlpha A γ 0 t) ≤ K) ∧
      (∀ j t, 1 ≤ j → j < t → matNorm (lemW A γ j t) ≤ K) ∧
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * ∑ j ∈ Finset.Ico 1 t, matNorm (lemW A γ j t))
        atTop (𝓝 0) := by sorry

end PolyakJuditsky.Averaging
