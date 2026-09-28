import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

theorem aux_itls_step {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) :
    ∀ k, R.x k ∈ box lo hi ∧ f (R.x k) ≤ f (R.x 0) := by
  intro k
  induction k with
  | zero => exact ⟨hR.x_zero_mem, le_rfl⟩
  | succ k ih =>
    rw [hR.x_succ k]
    split_ifs with h
    · exact ⟨hR.step_feasible k, le_trans h.le ih.2⟩
    · exact ih

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) :
    ∀ k, R.x k ∈ levelSet lo hi f (R.x 0) := by
  intro k
  exact aux_itls_step P lo hi f R hR k
