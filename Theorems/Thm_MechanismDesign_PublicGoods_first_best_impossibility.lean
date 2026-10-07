import Mathlib
import Definitions.Def_MechanismDesign_PublicGoods_Model

open MeasureTheory

namespace MechanismDesign.PublicGoods

/-- Börgers, Proposition 3.7 (p.50): an incentive-compatible and individually rational first best
mechanism exists if and only if either `N θ̲ ≥ c` or `N θ̄ ≤ c`. "First best" is (3.21)–(3.22):
decision rule `q*` and transfers summing to exactly `c q*(θ)` in every state `θ ∈ Θ`. -/
theorem first_best_impossibility {N : ℕ} (S : Setting N) :
    (∃ M : DirectMechanism N, M.IsDirect S ∧ M.IsFirstBest S ∧ M.IsIC S ∧ M.IsIR S) ↔
      (S.c ≤ (N : ℝ) * S.θlo ∨ (N : ℝ) * S.θhi ≤ S.c) := by sorry

end MechanismDesign.PublicGoods

