import Mathlib

namespace CalibratedCE.Generic

/-- A probability vector on a finite set `α`: nonnegative entries summing to one. -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- A joint distribution over `S(1) × S(2) = Fin m × Fin n`. -/
def IsJointDist {m n : ℕ} (D : Fin m → Fin n → ℝ) : Prop :=
  (∀ a b, 0 ≤ D a b) ∧ ∑ a, ∑ b, D a b = 1

/-- Correlated equilibrium of the two-player game `(u₁, u₂)` (players maximize), in the reduced
form of Foster–Vohra p. 44: a joint distribution `D` such that no player gains by composing their
recommendation with a deviation map `Φ`. -/
def IsCE {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) (D : Fin m → Fin n → ℝ) : Prop :=
  IsJointDist D ∧
  (∀ Φ : Fin m → Fin m, ∑ a, ∑ b, D a b * u₁ (Φ a) b ≤ ∑ a, ∑ b, D a b * u₁ a b) ∧
  (∀ Φ : Fin n → Fin n, ∑ a, ∑ b, D a b * u₂ a (Φ b) ≤ ∑ a, ∑ b, D a b * u₂ a b)

/-- `π(G)`: the set of correlated equilibria of the game `(u₁, u₂)`. -/
def CESet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {D | IsCE u₁ u₂ D}

/-- `R₁` is a stationary deterministic best-reply function of player 1: at every forecast `p`
(a probability vector over player 2's strategies) it selects a best response to `p`. -/
def IsBestReply₁ {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (R₁ : (Fin n → ℝ) → Fin m) : Prop :=
  ∀ p, IsDist p → ∀ a', ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ (R₁ p) b

/-- `R₂` is a stationary deterministic best-reply function of player 2. -/
def IsBestReply₂ {m n : ℕ} (u₂ : Fin m → Fin n → ℝ) (R₂ : (Fin m → ℝ) → Fin n) : Prop :=
  ∀ q, IsDist q → ∀ b', ∑ a, q a * u₂ a b' ≤ ∑ a, q a * u₂ a (R₂ q)

/-- `M_b(x)`: the mixtures over player 2's strategies to which `a` is a best response of
player 1. -/
def Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m) : Set (Fin n → ℝ) :=
  {p | IsDist p ∧ ∀ a', ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ a b}

/-- `D_t(x, y)`: the fraction of the first `t` rounds (rounds `0, …, t-1`) in which player 1
plays `a` and player 2 plays `b`. At `t = 0` the value is `0`. -/
noncomputable def empDist {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ)
    (a : Fin m) (b : Fin n) : ℝ :=
  (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) / t

end CalibratedCE.Generic
