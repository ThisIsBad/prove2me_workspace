import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game

namespace CalibratedCE.Convergence

/-- `R₁` is a (stationary, deterministic) best-reply function of player 1: for every
probability vector `p` over player 2's strategies, `R₁ p` maximizes player 1's expected
payoff against `p`. -/
def IsBestReply₁ {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (R₁ : (Fin n → ℝ) → Fin m) : Prop :=
  ∀ p : Fin n → ℝ, IsDist p → ∀ a' : Fin m, ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ (R₁ p) b

/-- `R₂` is a (stationary, deterministic) best-reply function of player 2. -/
def IsBestReply₂ {m n : ℕ} (u₂ : Fin m → Fin n → ℝ) (R₂ : (Fin m → ℝ) → Fin n) : Prop :=
  ∀ q : Fin m → ℝ, IsDist q → ∀ b' : Fin n, ∑ a, q a * u₂ a b' ≤ ∑ a, q a * u₂ a (R₂ q)

/-- `M_b(x)`: the mixtures over player 2's strategies to which `x = a` is a best response of
player 1. -/
def Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m) : Set (Fin n → ℝ) :=
  {p | IsDist p ∧ ∀ a' : Fin m, ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ a b}

/-- `M_p(x)`: the mixtures over player 2's strategies at which player 1, using `R₁`, actually
plays `x = a`. -/
def Mp {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (a : Fin m) : Set (Fin n → ℝ) :=
  {p | IsDist p ∧ R₁ p = a}

end CalibratedCE.Convergence
