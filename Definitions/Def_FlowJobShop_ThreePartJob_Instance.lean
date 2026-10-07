import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- The two-machine job shop JS constructed in the proof of Lemma 7. Jobs
`j < 3t` each visit machines 0 and 1 for `a j` time. Job `3t`
has `2t` operations of length `b`, alternating between machines 1 and 0. -/
def reductionInstance (C : ThreePartition) : JobShopLTAS.Core.Instance 2 (3 * C.t + 1) where
  μ j := if j.val < 3 * C.t then 2 else 2 * C.t
  π j i := if j.val < 3 * C.t then
      if i.val = 0 then 0 else 1
    else if i.val % 2 = 0 then 1 else 0
  p j _ := if h : j.val < 3 * C.t then (C.a ⟨j.val, h⟩ : ℝ) else (C.b : ℝ)
  p_nonneg j i := by
    split <;> positivity

/-- The finish-time threshold `τ = 2tB` in Lemma 7. -/
def threshold (C : ThreePartition) : ℝ := (2 * C.t * C.b : ℕ)

end FlowJobShop.ThreePartJob
