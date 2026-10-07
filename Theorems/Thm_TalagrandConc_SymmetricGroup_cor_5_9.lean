import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem cor_5_9 {N : ℕ} (hIH : Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hji : j ≠ i) :
    uniformAvg (G' N i) (fun σ => exp16 (fpm A σ (σ⁻¹ j) (Fin.last N)))
      ≤ (uniformProb (G' N i) A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup

