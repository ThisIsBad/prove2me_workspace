import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem cor_5_5 {N : ℕ} (hIH : Ineq53 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hij : i ≠ j) :
    uniformAvg (G N i) (fun σ => exp16 (fpm A σ j i)) ≤ (uniformProb (G N i) A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup

