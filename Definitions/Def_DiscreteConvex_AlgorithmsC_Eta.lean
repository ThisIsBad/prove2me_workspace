import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_RhoTilde
import Definitions.Def_DiscreteConvex_AlgorithmsC_ReachSet

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `η = max_{u∈U} [ρ̃(R(u)) - ρ̃(R(u)∖{u})]`, Eq. (10.26). -/
noncomputable def Eta {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U] (rho : Finset V → ℤ)
    (Gamma : U → Finset V) (Z : Finset V) (F : U → U → Prop) : ℤ :=
  (Finset.univ : Finset U).sup' Finset.univ_nonempty
    (fun u => RhoTilde rho Gamma Z (ReachSet F u) - RhoTilde rho Gamma Z ((ReachSet F u).erase u))

-- ===== L-convex functions and the steepest descent algorithm (§10.3.1) =====

end DiscreteConvex.AlgorithmsC
