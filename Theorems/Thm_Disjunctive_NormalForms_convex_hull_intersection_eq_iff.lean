import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Theorem 4.8 (Balas §4.3, p. 53-54): equality in Lemma 4.6 holds exactly when every extreme
point and every extreme direction of the intersection of the two closed convex hulls already
comes from a single pair of polyhedra `P_i ∩ P_k`. -/
theorem convex_hull_intersection_eq_iff {n : ℕ} {Q1 Q2 : Type*} [Fintype Q1] [Fintype Q2]
    (m1 : Q1 → ℕ) (A1 : (i : Q1) → Matrix (Fin (m1 i)) (Fin n) ℝ) (b1 : (i : Q1) → Fin (m1 i) → ℝ)
    (m2 : Q2 → ℕ) (A2 : (i : Q2) → Matrix (Fin (m2 i)) (Fin n) ℝ) (b2 : (i : Q2) → Fin (m2 i) → ℝ) :
    closure (convexHull ℝ
          ((⋃ i : Q1, Poly (A1 i) (b1 i)) ∩ (⋃ i : Q2, Poly (A2 i) (b2 i)))) =
        closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
          closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i))) ↔
      (∀ x ∈ Set.extremePoints ℝ
            (closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
              closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i)))),
          ∃ i k, x ∈ Set.extremePoints ℝ (Poly (A1 i) (b1 i) ∩ Poly (A2 k) (b2 k))) ∧
        (∀ y ∈ ExtremeDirections
              (closure (convexHull ℝ (⋃ i : Q1, Poly (A1 i) (b1 i))) ∩
                closure (convexHull ℝ (⋃ i : Q2, Poly (A2 i) (b2 i)))),
            ∃ i k, y ∈ ExtremeDirections (Poly (A1 i) (b1 i) ∩ Poly (A2 k) (b2 k))) := by sorry

end Disjunctive.NormalForms

