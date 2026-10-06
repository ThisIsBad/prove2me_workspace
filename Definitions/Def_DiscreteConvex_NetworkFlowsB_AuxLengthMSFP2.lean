import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary
import Definitions.Def_DiscreteConvex_NetworkFlowsB_DirDeriv

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The arc-length function `ℓξ` of Eq. (9.71). -/
noncomputable def AuxLengthMSFP2 (tail head : A → V) (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) :
    A ⊕ A ⊕ (V × V) → WithTop ℝ
  | .inl a => (gamma a : WithTop ℝ)
  | .inr (.inl a) => ((-gamma a : ℝ) : WithTop ℝ)
  | .inr (.inr (u, v)) =>
      DirDeriv f (Boundary tail head xi)
        (fun w => -(if w = u then (1:ℝ) else 0) + (if w = v then (1:ℝ) else 0))

-- ===== Integer versions (MSFP3, MSFP2 for integer flows) =====

end DiscreteConvex.NetworkFlowsB
