import Mathlib

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §4 I, pp. 301–302, in affine form. Weyl's inhomogeneous space `R̄_{n-1}` is the
hyperplane `x_n = -1` of `ℝⁿ`; here it is `ℝᵐ` with `m = n - 1`, a point `x` standing for
`(x, -1)`. A homogeneous half-space `(α x) ≥ 0` with `α = (a, a₀) ≠ 0` then reads
`a ⬝ᵥ x - a₀ ≥ 0`. It is an *extreme support* of the finite point system `S ⊆ ℝᵐ` when every
point of `S` satisfies it and equality holds at `n - 1 = m` points of `S` whose homogenized
points `(t, -1)` are linearly independent, i.e. at `m` affinely independent points of `S`. -/
def IsExtremeAffineSupport {m : ℕ} (S : Finset (Fin m → ℝ)) (a : Fin m → ℝ) (a₀ : ℝ) : Prop :=
  (a ≠ 0 ∨ a₀ ≠ 0) ∧ (∀ s ∈ S, 0 ≤ a ⬝ᵥ s - a₀) ∧
    ∃ T : Finset (Fin m → ℝ), T ⊆ S ∧ T.card = m ∧
      AffineIndependent ℝ (fun t : T => (t : Fin m → ℝ)) ∧ ∀ t ∈ T, a ⬝ᵥ t - a₀ = 0

/-- Weyl (1935), §4 I, p. 301: a *konvexes Polyeder* in `R̄_{n-1} = ℝᵐ` is the convex hull `H`
of a finite **non-degenerate** point system `S`. For points of the hyperplane `x_n = -1`,
non-degeneracy of the homogenized system is the statement that the affine span of `S` is the
whole space. -/
def IsConvexPolyhedron {m : ℕ} (H : Set (Fin m → ℝ)) : Prop :=
  ∃ S : Finset (Fin m → ℝ), affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤ ∧
    H = convexHull ℝ (S : Set (Fin m → ℝ))

/-- Weyl (1935), §4 II, p. 302: the region `H ⊆ R̄_{n-1} = ℝᵐ` cut out by finitely many
inequalities `(α x) ≡ α₁x₁ + ⋯ + α_{n-1}x_{n-1} - α_n ≥ 0`, one for each index `j`, with
`A j = (α₁, …, α_{n-1})` and `b j = α_n`. -/
def inequalityRegion {m : ℕ} {J : Type*} (A : J → Fin m → ℝ) (b : J → ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ j, 0 ≤ A j ⬝ᵥ x - b j}

end WeylPolyhedra.Polyhedron
