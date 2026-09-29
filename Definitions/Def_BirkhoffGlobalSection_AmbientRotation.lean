import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Mathlib.Data.Complex.Basic

namespace BirkhoffGlobalSection

noncomputable section

/-- The complex-linear part of a real linear map in the convention
`(q,p) ↦ q - i p`. For real blocks `A,B,C,D`, this is
`(A + D + i (B - C)) / 2`. The Hamiltonian complex structure `qI`
acts as multiplication by `i` in this convention. -/
def ambientComplexLinearPart (M : Phase →L[ℝ] Phase) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  Complex.mk
    ((M (coordinateVector (j.castAdd 2)) (i.castAdd 2) +
      M (coordinateVector (j.natAdd 2)) (i.natAdd 2)) / 2)
    ((M (coordinateVector (j.natAdd 2)) (i.castAdd 2) -
      M (coordinateVector (j.castAdd 2)) (i.natAdd 2)) / 2)

/-- The unnormalized determinant whose phase is the complex-linear-part
rotation map on the symplectic group. It is nonzero for symplectic maps;
nonvanishing is a theorem, not an assumption in this definition. -/
def ambientRotationDet (M : Phase →L[ℝ] Phase) : ℂ :=
  (ambientComplexLinearPart M).det

/-- A continuous real lift of the argument of the ambient determinant.
The positive radius avoids any convention for the argument at zero. -/
def IsAmbientRotationAngle (Y : ℝ → (Phase →L[ℝ] Phase))
    (α : ℝ → ℝ) : Prop :=
  Continuous α ∧ ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
    ambientRotationDet (Y t) =
      Complex.mk (ρ * Real.cos (α t)) (ρ * Real.sin (α t))

/-- The identity-normalized fundamental solution of the Hamiltonian
variational equation along `x`. -/
def IsHamiltonianVariationalSolution (F : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase)) : Prop :=
  Y 0 = ContinuousLinearMap.id ℝ Phase ∧
    ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x t)).comp (Y t)) t

end

end BirkhoffGlobalSection
