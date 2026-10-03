import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_RhoTilde
import Definitions.Def_DiscreteConvex_AlgorithmsB_ReachSet

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `η = max_{u∈U} [ρ̃(R(u)) - ρ̃(R(u)∖{u})]`, Eq. (10.26). -/
noncomputable def Eta {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U] (rho : Finset V → ℤ)
    (Gamma : U → Finset V) (Z : Finset V) (F : U → U → Prop) : ℤ :=
  (Finset.univ : Finset U).sup' Finset.univ_nonempty
    (fun u => RhoTilde rho Gamma Z (ReachSet F u) - RhoTilde rho Gamma Z ((ReachSet F u).erase u))

-- ===== Theorems =====

end DiscreteConvex.AlgorithmsB
