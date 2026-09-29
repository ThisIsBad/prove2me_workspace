import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm

namespace RockafellarMaxMono.Cyclic

theorem conj_add_halfSqNorm_finite_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hlsc : LowerSemicontinuous f) :
    ∃ h : StrongDual ℝ E → ℝ, Continuous h ∧
      ∀ x' : StrongDual ℝ E, Shared.conj (fun y => f y + Shared.halfSqNorm y) x' = ((h x' : ℝ) : EReal) := by sorry

end RockafellarMaxMono.Cyclic

