import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 90, Proposition 5.14: for the multiplicative mapping
`H(x, u, J) = E{g(x, u, w) J[f(x, u, w)] | x, u}` of Section 2.3.4 (countable `W`) with
`J₀ ≡ 1`:
(a) if `1 ≤ g(x, u, w) ≤ b` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, with `b ∈ ℝ`, then I, I.1 and I.2
hold, the scalar in I.2 being `b`;
(b) if `0 ≤ g(x, u, w) ≤ 1` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then D, D.1 and D.2 hold, the
scalar in D.2 being `1`.
A model of Part I with this `H` and `J₀` is any `Model` whose fields `H` and `Jbar` are these. -/
theorem prop5_14_multiplicative_assumptions {S C W : Type*} [Countable W]
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      ∀ b : ℝ, (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 1 ≤ g x u w ∧ g x u w ≤ (b : EReal)) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 b) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ 1) →
        m.AssumptionD ∧ m.AssumptionD1 ∧ m.AssumptionD2 1) := by sorry

end BertsekasShreve.Monotone

