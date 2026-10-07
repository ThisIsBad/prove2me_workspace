import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Proposition 11.2**, p.209. An (admissible) direct mechanism is incentive-compatible if and
only if it satisfies (11.1) and (11.2): `U(τ) ≥ Û(τ′|τ)` for all `τ, τ′ ∈ [τ̲, τ̄]`. -/
theorem ic_iff {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) :
    m.IsIC E ↔ m.IsExPostIC ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ τ' ∈ Set.Icc τlo τhi, m.Uhat E τ' τ ≤ m.U E τ := by sorry

end MechanismDesign.Dynamic

