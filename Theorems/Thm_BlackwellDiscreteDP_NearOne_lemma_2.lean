import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

/-- **Lemma 2.** For any `f, g ∈ F` for which `g(s) ∈ E(s, f)` for all `s`, we have
`x(g) = x(f)`. If in addition `Q*(g)Q*(f) = Q*(g)`, then `y(g) = y(f)`.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 724, Lemma 2. -/
theorem lemma_2 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f g : St → Act) (hE : ∀ s, g s ∈ M.gainBiasEqualSet f s) :
    M.x g = M.x f ∧ (M.Qstar g * M.Qstar f = M.Qstar g → M.y g = M.y f) := by sorry

end BlackwellDiscreteDP.NearOne

