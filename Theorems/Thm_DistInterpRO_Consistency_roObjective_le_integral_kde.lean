import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem roObjective_le_integral_kde {V : Type*} {m n : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (hfm : ∀ v, Measurable (f v)) (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (xs : Fin n → Fin m → ℝ) (v : V) :
    roObjective f ε xs v ≤ ∫ x, f v x * kde ε xs x := by sorry

end DistInterpRO.Consistency
