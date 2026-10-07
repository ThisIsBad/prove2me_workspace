import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.7**, p.216. An (admissible) incentive-compatible direct mechanism is
individually rational if and only if `U(τ̲) ≥ 0`. -/
theorem ir_iff {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    m.IsIR E ↔ 0 ≤ m.U E τlo := by sorry

end MechanismDesign.Dynamic

