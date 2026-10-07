import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_7 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (σ : Perm (Fin (N + 1)))
    (j : Fin (N + 1)) (hj : j ≠ σ (Fin.last N)) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ (Fin.last N) ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2)
      + ENNReal.ofReal (1 - lam) * g A σ (Fin.last N) (σ⁻¹ j)
      + ENNReal.ofReal lam * fpm A σ (σ⁻¹ j) (Fin.last N) := by sorry
end TalagrandConc.SymmetricGroup

