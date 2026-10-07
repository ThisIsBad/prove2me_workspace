import Mathlib
import Definitions.Def_CostScaling_StrongPoly_IsEpsTight
import Definitions.Def_CostScaling_StrongPoly_fixedArcs

namespace CostScaling.StrongPoly

open CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lemma 4.4, p. 17: when the error parameter drops by a factor of `2n`, the
set of fixed arcs grows strictly. Positive `ε` is required by the proof and by
the statement's truth at the boundary. -/
theorem lemma_4_4_fixedArcs_strict (N : CircNetwork V)
    (hvertices : 2 ≤ Fintype.card V)
    (harcs : Fintype.card V - 1 ≤ N.E.card)
    (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 ≤ ε')
    (hscale : ε' ≤ ε / (2 * (Fintype.card V : ℝ)))
    (htight : ∃ f : V → V → ℝ, IsEpsTight N f ε) :
    fixedArcs N ε ⊂ fixedArcs N ε' := by sorry

end CostScaling.StrongPoly

