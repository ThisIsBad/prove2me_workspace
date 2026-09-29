import Definitions.Def_BirkhoffGlobalSection_TangentialHessian

namespace BirkhoffGlobalSection

noncomputable section

/-- Coordinates of `w` against the quaternionic vectors `J g` and `K g` of the
frame `I g, J g, K g` built from a gradient `g`. On the tangent space `g^⊥` of
a regular level set they vanish exactly on the Hamiltonian direction `I g`, so
they trivialize the transverse plane bundle of the level set. With this order,
positive rotation is counterclockwise: along a Hopf fiber of the round sphere
the linearized flow turns every transverse vector twice per period. -/
def transverseFrameCoordinates (g w : Phase) : Plane :=
  ![w ⬝ᵥ TangentialHessian.frame g 1, w ⬝ᵥ TangentialHessian.frame g 2]

/-- `x` solves Hamilton's equations for `F`, stays in `S`, and closes up after
the time `T > 0`. The time `T` need not be the least period. -/
def IsPeriodicHamiltonianSolutionIn (F : Phase → ℝ) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ) : Prop :=
  0 < T ∧ (∀ t : ℝ, x t ∈ S) ∧
    (∀ t : ℝ, HasDerivAt x (hamiltonianVectorField F (x t)) t) ∧
    x T = x 0

/-- Along the closed solution `x` of period `T`, the linearized flow turns every
tangent vector transverse to the flow by more than one full turn, measured
in the frame coordinates `transverseFrameCoordinates`. The linearized flow is
the solution `Y` of the variational equation with `Y 0 = id`. The angle is any
continuous polar angle of the frame coordinates.

This is the winding-interval form of the condition that the Conley--Zehnder
index of `(x, T)` is at least `3`, in the global frame. Degenerate orbits use
the lower semicontinuous extension of the index. -/
def HasTransverseWindingAboveOne (F : Phase → ℝ) (x : ℝ → Phase) (T : ℝ) :
    Prop :=
  ∀ Y : ℝ → (Phase →L[ℝ] Phase),
    Y 0 = ContinuousLinearMap.id ℝ Phase →
    (∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField F) (x t)).comp (Y t)) t) →
    ∀ v : Phase, fderiv ℝ F (x 0) v = 0 →
      transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0 →
      ∀ θ : ℝ → ℝ, Continuous θ →
        (∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
          transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
            ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) →
        2 * Real.pi < θ T - θ 0

/-- Dynamical convexity of the Hamiltonian flow of `F` on `S`: every closed
solution in `S`, including every multiple cover, has transverse winding above
one. Equivalently, every periodic orbit in `S` has Conley--Zehnder index at
least `3` in the global quaternionic frame. On the Levi-Civita cover, closed
orbits are exactly the lifts of contractible orbits of the regularized
quotient, so this is dynamical convexity of that quotient. -/
def IsDynamicallyConvexOn (F : Phase → ℝ) (S : Set Phase) : Prop :=
  ∀ (x : ℝ → Phase) (T : ℝ), IsPeriodicHamiltonianSolutionIn F S x T →
    HasTransverseWindingAboveOne F x T

end

end BirkhoffGlobalSection
