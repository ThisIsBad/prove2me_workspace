import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.6 (Bertsekas & Shreve 1996, p. 50). Let `m` be a model whose mapping is the
multiplicative-cost mapping `H(x, u, J) = E{g(x, u, w) J[f(x, u, w)] | x, u}` of Section 2.3.4
(eq. (33) of Chapter 3), with `w` in a countable set `W` distributed according to
`p(· | x, u)`, and `g(x, u, w) ≥ 0` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W` (eq. (27) of
Chapter 2). Then `H` satisfies F.1. If there is `b ∈ R` with `0 ≤ g(x, u, w) ≤ b` for all
`x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then `H` satisfies F.2, with the inequality of F.2 holding for
the constant `α = b`. -/
theorem multiplicative_F1_F2 {S C W : Type*} [Countable W] (m : Model S C)
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S)
    (hg : ∀ x, ∀ u ∈ m.U x, ∀ w, 0 ≤ g x u w)
    (hH : m.H = multiplicativeH p g f) :
    m.AssumptionF1 ∧
    ∀ b : ℝ, (∀ x, ∀ u ∈ m.U x, ∀ w, g x u w ≤ (b : EReal)) →
      m.AssumptionF2 ∧ m.F2With b := by sorry

end BertsekasShreve.FiniteHorizon

