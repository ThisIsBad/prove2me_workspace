import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, Proposition 4.1, assumption A1, p. 12 ("or equivalently"): under the standing
assumptions on `γ`, for every `T > 0` the sum form of A1,
`lim_{n→∞} sup{‖Σ_{i=n}^{k−1} γ_{i+1} U_{i+1}‖ : k = n + 1, …, m(τ_n + T)} = 0`,
holds if and only if `lim_{t→∞} Δ(t, T) = 0`, where `Δ(t, T) = sup_{0≤h≤T} ‖∫_t^{t+h} Ū(s) ds‖`. -/
theorem a1At_iff_tendsto_delta {d : ℕ} (γ : ℕ → ℝ) (hγ : IsStepSizeSeq γ)
    (U : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℝ) (hT : 0 < T) :
    A1At γ U T ↔ Tendsto (fun t : ℝ => Delta γ U t T) atTop (𝓝 0) := by sorry

end StochApproxDyn.Interpolation

