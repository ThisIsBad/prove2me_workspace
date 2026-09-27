import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Data.Real.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Grünbaum (2003), §2.3, Theorem 5 (2.3.5), printed p. 15 / PDF p. 33.
Every point in the convex hull of an arbitrary subset of real d-space is
represented using d+1 points of that subset. Repetitions and zero weights
are allowed, exactly as in the source. Statement-only local staging.
Mathlib's `convexHull_eq_union` gives the compatible affine-independent
finite-support formulation; no new convex-hull adapter is introduced. -/
theorem caratheodory_convex_representation (d : ℕ)
    (A : Set (Fin d → ℝ)) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ A) :
    ∃ (v : Fin (d + 1) → Fin d → ℝ) (w : Fin (d + 1) → ℝ),
      (∀ i, v i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧
        (∑ i, w i) = 1 ∧ x = ∑ i, w i • v i := by sorry

end Grunbaum2003
