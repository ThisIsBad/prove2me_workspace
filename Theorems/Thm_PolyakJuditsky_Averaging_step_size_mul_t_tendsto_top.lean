import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open Filter Topology

namespace PolyakJuditsky.Averaging

/-- Lemma 1, proof Part 2 (p. 845): under condition (4) of Assumption 2.2, `t γ_t → ∞`. -/
theorem step_size_mul_t_tendsto_top (γ : ℕ → ℝ) (hγ : StepCondition4 γ) :
    Tendsto (fun t : ℕ => (t : ℝ) * γ t) atTop atTop := by sorry

end PolyakJuditsky.Averaging
