import Mathlib
import Definitions.Def_SecretaryWD_Graphic_PartitionSecretary

namespace SecretaryWD.Graphic
theorem partition_secretary_competitive {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) (hP : IsPartitionOf E P)
    (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ π : Equiv.Perm (Fin E.card), IsPartIndep P (partitionSecretaryOutput E v P π)) ∧
      partitionValue P v ≤
        Real.exp 1 * SecretaryWD.DiscUpper.uniformAvg fun π => partitionSecretaryValue E v P π := by sorry
end SecretaryWD.Graphic

