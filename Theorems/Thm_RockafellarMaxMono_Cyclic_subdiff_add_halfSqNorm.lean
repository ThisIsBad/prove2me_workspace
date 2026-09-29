import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm
open Pointwise

namespace RockafellarMaxMono.Cyclic

theorem subdiff_add_halfSqNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.subdiff (fun y => f y + Shared.halfSqNorm y) x = Shared.subdiff f x + Shared.subdiff Shared.halfSqNorm x := by sorry

end RockafellarMaxMono.Cyclic

