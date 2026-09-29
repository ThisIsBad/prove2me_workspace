import Mathlib

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §3, p. 296, (9): the finite point system `S ⊆ ℝⁿ` read as the system of
homogeneous linear inequalities `a ⬝ᵥ ξ ≥ 0` (`a ∈ S`); `(S)` is the region of the dual space
cut out by them. -/
def solutionRegion {n : ℕ} (S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {ξ | ∀ a ∈ S, 0 ≤ a ⬝ᵥ ξ}

/-- Weyl (1935), §3, p. 296, Satz 4: `ξ` is an *extreme Lösung* (extreme solution) of the
inequality system `S` when equality `a ⬝ᵥ ξ = 0` holds in `n - 1` linearly independent
inequalities `a` of `S`. Added, as implicit in the word "Lösung" and in the identification of
solutions on a ray (p. 290, p. 297): `ξ` solves the system (`ξ ∈ (S)`) and `ξ ≠ 0`. -/
def IsExtremeSolution {n : ℕ} (S : Finset (Fin n → ℝ)) (ξ : Fin n → ℝ) : Prop :=
  ξ ∈ solutionRegion S ∧ ξ ≠ 0 ∧
    ∃ T : Finset (Fin n → ℝ), T ⊆ S ∧ T.card = n - 1 ∧
      LinearIndependent ℝ (fun t : T => (t : Fin n → ℝ)) ∧ ∀ a ∈ T, a ⬝ᵥ ξ = 0

/-- Weyl (1935), §3, p. 297, (10): the region `(Σ)` of the dual system `Σ`, whose inequalities
are `α ⬝ᵥ x ≥ 0` for **all** extreme solutions `α` of `S` (positive multiples of an extreme
solution give the same inequality, so no representatives are chosen). -/
def dualRegion {n : ℕ} (S : Finset (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ α : Fin n → ℝ, IsExtremeSolution S α → 0 ≤ α ⬝ᵥ x}

end WeylPolyhedra.Polyhedron
