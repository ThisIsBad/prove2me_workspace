import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_6 {N : ℕ} (hIH : Ineq53 N ∨ Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hji : j ≠ i) :
    uniformAvg (G N i) (fun σ => exp16 (g A σ i j)) ≤ (uniformProb (G N j) A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup

