import Mathlib

namespace Nullstellensatz

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The algebraic set `V(J) ⊆ Kⁿ`: the common zeros of all polynomials in `J`. -/
def zeroSet (J : Ideal (MvPolynomial (Fin n) K)) : Set (Fin n → K) :=
  {a | ∀ f ∈ J, eval a f = 0}

/-- The vanishing ideal `I(U)`: all polynomials vanishing at every point of `U`. -/
def vanishingIdeal (U : Set (Fin n → K)) : Ideal (MvPolynomial (Fin n) K) where
  carrier := {p | ∀ a ∈ U, eval a p = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq a ha
    simp [hp a ha, hq a ha]
  smul_mem' := by
    intro c p hp a ha
    simp [hp a ha]

/-- `W ⊆ Kⁿ` is an algebraic set: `W = V(J)` for some ideal `J`. -/
def IsAlgebraicSet (W : Set (Fin n → K)) : Prop :=
  ∃ J : Ideal (MvPolynomial (Fin n) K), W = zeroSet J

/-- `W` is irreducible in the Zariski topology: it is nonempty and whenever it is covered by
two algebraic sets (Zariski-closed sets), it is contained in one of them. -/
def IsZariskiIrreducible (W : Set (Fin n → K)) : Prop :=
  W.Nonempty ∧ ∀ W₁ W₂ : Set (Fin n → K), IsAlgebraicSet W₁ → IsAlgebraicSet W₂ →
    W ⊆ W₁ ∪ W₂ → W ⊆ W₁ ∨ W ⊆ W₂

/-- The ideal `(X₁ - a₁, …, Xₙ - aₙ)` of the point `a ∈ Kⁿ`. -/
noncomputable def pointIdeal (a : Fin n → K) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range fun i => X i - C (a i))

end Nullstellensatz
