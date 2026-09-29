import Mathlib
import Definitions.Def_SupplyChainFactoring_Extension_Model

namespace SupplyChainFactoring.Extension

/-- Eq. (12), p. 6082: the supplier's best response under reverse factoring at `(w, τ)`.
If `c_𝓡(τ) < w`, the best responses are exactly the `q ∈ (0, Z)` with `w F̄(q) = c_𝓡(τ)`;
if `w ≤ c_𝓡(τ)`, the only best response is `q = 0`. -/
theorem reverse_best_response (M : Model) {Cs Cr w τ : ℝ}
    (hCs : Cs ∈ Set.Ioo M.Cmin M.Cmax) :
    (M.cR Cs Cr τ < w → ∀ q : ℝ,
      M.IsBestResponse (M.ΛR Cr τ) Cs w q ↔ (M.InSupport q ∧ w * M.Fbar q = M.cR Cs Cr τ)) ∧
    (w ≤ M.cR Cs Cr τ → ∀ q : ℝ, M.IsBestResponse (M.ΛR Cr τ) Cs w q ↔ q = 0) := by sorry

end SupplyChainFactoring.Extension
