import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.12 (Myerson and Satterthwaite, 1983), p.66: a well-defined,
incentive-compatible, individually rational and ex post budget balanced direct mechanism whose
trading rule is first best (any tie rule) exists if and only if `θ̲_B ≥ θ̄_S` or `θ̲_S ≥ θ̄_B`. -/
theorem myerson_satterthwaite (E : Environment) :
    (∃ m : DirectMechanism E, m.Admissible ∧ m.ExPostBB ∧ IsFirstBestRule E m.q) ↔
      (E.hiS ≤ E.loB ∨ E.hiB ≤ E.loS) := by sorry

end MechanismDesign.BilateralTrade

