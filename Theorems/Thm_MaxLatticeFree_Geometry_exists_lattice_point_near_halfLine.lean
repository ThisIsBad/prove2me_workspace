import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf

namespace MaxLatticeFree.Geometry

theorem exists_lattice_point_near_halfLine {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Λ) (r : EuclideanSpace ℝ (Fin n)) (hrV : r ∈ V) (hr0 : r ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ z ∈ Λ, z ≠ y ∧
      Metric.infDist z {p : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, lam ≤ t ∧ p = y + t • r} < ε := by sorry

end MaxLatticeFree.Geometry
