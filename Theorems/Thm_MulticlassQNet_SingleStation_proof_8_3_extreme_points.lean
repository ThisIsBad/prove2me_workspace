import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra

namespace MulticlassQNet.SingleStation

/-- Proof of Theorem 8.3 (p. 37): P1 is an (extended) polymatroid base whose extreme points are
exactly the vectors `v(π)` of (58), one per permutation `π` of the classes, and every point of P1
is a convex combination of them. -/
theorem proof_8_3_extreme_points {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    Set.extremePoints ℝ (P1 lam mu) = Set.range (v lam mu) ∧
      P1 lam mu = convexHull ℝ (Set.range (v lam mu)) := by sorry

end MulticlassQNet.SingleStation

