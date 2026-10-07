import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- p. 459: for a nonsingular integer `m × m` matrix `B`, the factor group
`𝒢 = M(I)/M(B)` is finite and `|𝒢| = |det B|`. -/
theorem card_factorGroup {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hdet : B.det ≠ 0) :
    Finite (FactorGroup B) ∧ Nat.card (FactorGroup B) = detAbs B := by sorry

end Gomory69.Asymptotic

