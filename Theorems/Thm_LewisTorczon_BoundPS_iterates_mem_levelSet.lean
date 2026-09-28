import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- §4, p. 10, proof of Theorem 4.5, second paragraph: all the iterates of a generalized pattern
search run lie in `L_Ω(x_0) = {x ∈ Ω : f(x) ≤ f(x_0)}`. -/
theorem iterates_mem_levelSet {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) :
    ∀ k, R.x k ∈ levelSet lo hi f (R.x 0) := by sorry

end LewisTorczon.BoundPS
