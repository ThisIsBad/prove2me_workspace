import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform

namespace TeschlQM.SelfAdjoint

/-- Teschl, Lemma 2.27 (p. 83): for a symmetric `A` with Cayley transform `V`, the following are
equivalent: `A` is closed; `𝔇(V) = Ran(A + i)` is closed; `Ran(V) = Ran(A - i)` is closed;
`V` is closed. -/
theorem isClosed_tfae_cayley {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A V : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (hV : IsCayleyTransform A V) :
    List.TFAE [A.IsClosed, IsClosed (V.domain : Set H), IsClosed (Set.range V), V.IsClosed] := by sorry

end TeschlQM.SelfAdjoint
