import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- Proof of THEOREM 4 (p. 462): if `y ∈ K_B(d)` and `v` has Euclidean length at most `d`,
then `y − v ∈ K_B`. -/
theorem sub_mem_basisCone {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0)
    (d : ℝ) (y v : Fin m → ℝ) (hy : y ∈ deepCone B d) (hv : euclNorm v ≤ d) :
    y - v ∈ basisCone B := by sorry

end Gomory69.Asymptotic

