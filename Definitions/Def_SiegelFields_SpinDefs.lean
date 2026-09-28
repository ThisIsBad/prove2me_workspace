import Mathlib


open Matrix Complex

namespace SiegelFields

/-- The imaginary, hermitian matrix `C = [[0, -i], [i, 0]]` (Siegel, *Fields*, §IIA1, p. 112). -/
def matC : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- A 2×2 complex matrix represents a 3-vector when it is hermitian and traceless
(Siegel, *Fields*, §IIA1, p. 111: `V = V†`, `tr V = 0`). -/
def IsThreeVector (V : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  V.IsHermitian ∧ V.trace = 0

/-- The book's basis (§IIA1, p. 111):
`V = (1/√2) [[V¹, V² - i V³], [V² + i V³, -V¹]]`, with components indexed `0, 1, 2`. -/
noncomputable def vecToMatrix (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    !![(v 0 : ℂ), (v 1 : ℂ) - I * (v 2 : ℂ); (v 1 : ℂ) + I * (v 2 : ℂ), -(v 0 : ℂ)]

/-- The `i`-th basis 3-vector as a 2×2 matrix, `E_i = vecToMatrix (e_i)`. -/
noncomputable def basisMatrix (i : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  vecToMatrix (Pi.single i 1)

/-- The real 3×3 matrix of the transformation `V ↦ U V U†` in the book's basis:
`R(U)_{ij} = Re tr(E_i U E_j U†)`. -/
noncomputable def rotationOf (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (trace (basisMatrix i * U * basisMatrix j * Uᴴ)).re

end SiegelFields
