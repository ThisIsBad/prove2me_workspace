import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Theorem 4(e).** For any `f₀` for which `G(s, f₀)` is empty for all `s`, `x(f₀) ≧ x(g)` for
all `g`. Denote by `F*` the set of all `g` such that `x(g) = x(f₀)`. There is an `f* ∈ F*` with
`y(f*) ≧ y(g)` for all `g ∈ F*`. The nearly optimal `g`'s are exactly those for which
`x(g) = x(f*)` and `y(g) = y(f*)`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(e).

**Formalization Note.** All three assertions are in one statement so that the `f*` of the third
is the `f*` of the second. `≧` is coordinatewise; `g` ranges over all decision rules `F`; a rule
`g` is "nearly optimal" when the stationary policy `g^(∞)` is (`IsNearlyOptimal`, the §4 notion,
against all policies). -/
theorem theorem_4e {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f₀ : St → Act) (hG : ∀ s, M.gainBiasImprovementSet f₀ s = ∅) :
    (∀ g : St → Act, M.x g ≤ M.x f₀) ∧
      ∃ fstar : St → Act, M.x fstar = M.x f₀ ∧
        (∀ g : St → Act, M.x g = M.x f₀ → M.y g ≤ M.y fstar) ∧
        ∀ g : St → Act,
          (M.IsNearlyOptimal (Policy.stationary g) ↔ M.x g = M.x fstar ∧ M.y g = M.y fstar) := by sorry

end BlackwellDiscreteDP.NearOne

