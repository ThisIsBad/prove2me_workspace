import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Lemma 11.1**, p.211. If an (admissible) direct mechanism is incentive-compatible, then
`U(τ)` is increasing and absolutely continuous on `[τ̲, τ̄]`. -/
theorem U_monotone_absolutelyContinuous {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    MonotoneOn (m.U E) (Set.Icc τlo τhi) ∧ AbsolutelyContinuousOnInterval (m.U E) τlo τhi := by sorry

end MechanismDesign.Dynamic

