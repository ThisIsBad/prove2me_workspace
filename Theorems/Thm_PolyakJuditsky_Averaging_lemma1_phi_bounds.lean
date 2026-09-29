import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

/-- Lemma 1 (p. 844), under condition (4) with `γ_t > 0` for all `t ≥ 0` and `Re λ_i(A) > 0`:
there is `K < ∞` with `‖φ_j^t‖ ≤ K` for all `j` and `t ≥ j` (A2), and
`(1/t) ∑_{j=0}^{t-1} ‖φ_j^t‖ → 0` ((A3) with the norm inside, the form its proof establishes). -/
theorem lemma1_phi_bounds {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ)
    (hA : EigenRePos A) (hpos : ∀ t, 0 < γ t) (hγ : StepCondition4 γ) :
    ∃ K : ℝ, (∀ j t, j ≤ t → matNorm (lemPhi A γ j t) ≤ K) ∧
      Tendsto (fun t : ℕ => (t : ℝ)⁻¹ * ∑ j ∈ Finset.range t, matNorm (lemPhi A γ j t))
        atTop (𝓝 0) := by sorry

end PolyakJuditsky.Averaging
