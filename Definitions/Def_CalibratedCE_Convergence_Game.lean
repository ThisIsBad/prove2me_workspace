import Mathlib

namespace CalibratedCE.Convergence

/-- A probability vector on a finite set `α`: nonnegative entries summing to one. -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- A joint distribution on `Fin m × Fin n`, written as an `m × n` matrix. -/
def IsJointDist {m n : ℕ} (D : Fin m → Fin n → ℝ) : Prop :=
  (∀ a b, 0 ≤ D a b) ∧ ∑ a, ∑ b, D a b = 1

/-- Correlated equilibrium of the two-player game with payoff matrices `u₁ u₂` (both players
maximize), in the joint-distribution form of Foster–Vohra (1997), p. 44: no player gains by
applying a deviation map `Φ` to the strategy recommended to them. -/
def IsCE {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (D : Fin m → Fin n → ℝ) : Prop :=
  IsJointDist D ∧
  (∀ Φ : Fin m → Fin m, ∑ a, ∑ b, D a b * u₁ (Φ a) b ≤ ∑ a, ∑ b, D a b * u₁ a b) ∧
  (∀ Φ : Fin n → Fin n, ∑ a, ∑ b, D a b * u₂ a (Φ b) ≤ ∑ a, ∑ b, D a b * u₂ a b)

/-- `π(G)`: the set of correlated equilibria of the game `G = (u₁, u₂)`. -/
def CESet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {D | IsCE u₁ u₂ D}

end CalibratedCE.Convergence
