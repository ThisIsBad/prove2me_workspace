import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- THEOREM 4 (p. 462): let `B` be an optimal linear programming basis of (2), `D = |det B|`,
`l_max` the Euclidean length of the longest nonbasic column, and `b ∈ K_B(l_max (D − 1))`.
If `t*` is a vertex of `P(𝒢, 𝒩, f b)` minimizing (8) and `x_N*` the nonbasic part of a
corresponding vertex using only least cost columns, then `x_B* = B⁻¹(b − N x_N*)` is an
integer vector and `x* = (x_B*, x_N*)` is an optimal solution of the integer program (2). -/
theorem theorem_4 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) := by sorry

end Gomory69.Asymptotic

