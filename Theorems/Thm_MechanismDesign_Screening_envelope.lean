import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.2**, p.11. If a direct mechanism is incentive-compatible, then `u` is increasing and
convex on `[θ̲, θ̄]`, hence differentiable at all but countably many points of `(θ̲, θ̄)`, and
`u′(θ) = q(θ)` at every interior point `θ` at which `u` is differentiable. -/
theorem envelope {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    MonotoneOn m.u (Set.Icc θlo θhi) ∧ ConvexOn ℝ (Set.Icc θlo θhi) m.u ∧
      {θ ∈ Set.Ioo θlo θhi | ¬ DifferentiableAt ℝ m.u θ}.Countable ∧
      ∀ θ ∈ Set.Ioo θlo θhi, DifferentiableAt ℝ m.u θ → deriv m.u θ = m.q θ := by sorry

end MechanismDesign.Screening

