import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem box_oscillation {V : Type*} {m : ℕ} (f : V → (Fin m → ℝ) → ℝ) (C : ℝ)
    (hfC : ∀ v x, |f v x| ≤ C) (v : V) (xi : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (⨆ x : box xi ε, f v x) - (⨅ x : box xi ε, f v x) ≤ modulus f (2 * ε) := by sorry

end DistInterpRO.Consistency
