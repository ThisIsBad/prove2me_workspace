import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Theorem 4(d).** If for each `s`, `G(s, f)` is empty, and `g(s) ∈ E(s, f)` for all `s`
implies `Q*(g)Q*(f) = Q*(g)`, then `f` is nearly optimal.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 723, Theorem 4(d).

**Formalization Note.** The second hypothesis ranges over all decision rules `g ∈ F`. "Nearly
optimal" is the §4 notion `IsNearlyOptimal` (`U(β) − V_β → 0`, encoded without `U`, against all
policies), applied to `f^(∞)`. -/
theorem theorem_4d {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) (hG : ∀ s, M.gainBiasImprovementSet f s = ∅)
    (hE : ∀ g : St → Act, (∀ s, g s ∈ M.gainBiasEqualSet f s) →
      M.Qstar g * M.Qstar f = M.Qstar g) :
    M.IsNearlyOptimal (Policy.stationary f) := by sorry

end BlackwellDiscreteDP.NearOne

