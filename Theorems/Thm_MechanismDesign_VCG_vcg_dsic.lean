import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Proposition 7.4 (p.133): VCG mechanisms are dominant strategy incentive-compatible.
No structure is assumed on `A` or on the type sets. -/
theorem vcg_dsic {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (hM : IsVCG u M) : DSIC u M := by sorry

end MechanismDesign.VCG

