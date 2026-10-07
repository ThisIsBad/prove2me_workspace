import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem prop_5_2 {N : ℕ} (A : Set (Perm (Fin N))) (p : Fin N) :
    uniformAvg Finset.univ (fun σ => exp16 (fp A σ p)) ≤ (PN A)⁻¹ ∧
      uniformAvg Finset.univ (fun σ => exp16 (fp A σ (σ⁻¹ p))) ≤ (PN A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup

