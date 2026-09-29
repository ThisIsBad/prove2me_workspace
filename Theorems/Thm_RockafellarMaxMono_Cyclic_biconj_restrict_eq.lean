import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj

namespace RockafellarMaxMono.Cyclic

theorem biconj_restrict_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.conj (Shared.conj f) (NormedSpace.inclusionInDoubleDual ℝ E x) = f x := by sorry

end RockafellarMaxMono.Cyclic

