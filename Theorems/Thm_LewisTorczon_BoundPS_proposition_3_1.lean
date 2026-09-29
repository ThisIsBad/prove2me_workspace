import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 3.1** (6) and (8), p. 5: for `x ∈ Ω`, `‖q(x)‖ ≤ ‖g(x)‖`, and `x` is a stationary
point of problem (1) iff `q(x) = 0`. (Part (7) is not stated.) -/
theorem proposition_3_1 {n : ℕ} (lo hi : Fin n → EReal) (hlohi : ∀ j, lo j < hi j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ box lo hi) :
    ‖projQ lo hi f x‖ ≤ ‖gradient f x‖ ∧ (IsStationary lo hi f x ↔ projQ lo hi f x = 0) := by sorry

end LewisTorczon.BoundPS
