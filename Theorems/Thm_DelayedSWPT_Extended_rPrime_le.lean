import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Anderson and Potts (2004), §3.2, p. 689: the transformed release dates satisfy
`r′ⱼ ≤ max {2rⱼ, pⱼ}`. -/
theorem rPrime_le {n : ℕ} (I : Instance n) (j : Fin n) :
    rPrime I j ≤ max (2 * I.r j) (I.p j) := by sorry

end DelayedSWPT.Extended

