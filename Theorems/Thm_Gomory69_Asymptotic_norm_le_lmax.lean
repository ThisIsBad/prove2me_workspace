import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- Proof of THEOREM 4 (p. 462): if `t*` is a vertex of `P(𝒢, 𝒩, f b)` and `x_N*` the
nonbasic part of a corresponding vertex (Remark 1), then
`‖N x_N*‖ ≤ l_max (D − 1)`, `D = |det B|`, `‖·‖` the Euclidean length. -/
theorem norm_le_lmax {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hdet : B.det ≠ 0) (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    euclNorm (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) ≤ lmax N * ((detAbs B : ℝ) - 1) := by sorry

end Gomory69.Asymptotic

