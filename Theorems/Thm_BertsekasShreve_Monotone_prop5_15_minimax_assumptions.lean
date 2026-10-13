import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 90, Proposition 5.15: for the minimax mapping
`H(x, u, J) = sup_{w ∈ W(x, u)} {g(x, u, w) + α J[f(x, u, w)]}` of Section 2.3.5 (with `α > 0` and
`W(x, u)` nonempty for `x ∈ S`, `u ∈ U(x)`, the standing assumptions of that section) and
`J₀ ≡ 0`:
(a) if `0 ≤ g(x, u, w)` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then I, I.1 and I.2 hold, the scalar
in I.2 being `α`;
(b) if `g(x, u, w) ≤ 0` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then D and D.2 hold, the scalar in
D.2 being `α`. -/
theorem prop5_15_minimax_assumptions {S C W : Type*}
    (Wset : S → C → Set W) (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 α) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.minimaxH Wset g f α → m.Jbar = (fun _ => 0) →
      (∀ x : S, ∀ u ∈ m.U x, (Wset x u).Nonempty) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, g x u w ≤ 0) →
        m.AssumptionD ∧ m.AssumptionD2 α) := by sorry

end BertsekasShreve.Monotone

