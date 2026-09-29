import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration

namespace CalibratedCE.Generic

open Filter Topology

/-- The history of play generated when player `i` forecasts with the history-dependent rule `πᵢ`
and plays `Rᵢ` of that forecast: `hist 0 = []` and round `t` appends
`(R₁ (π₁ (hist t)), R₂ (π₂ (hist t)))`. -/
def hist {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ) :
    ℕ → List (Fin m × Fin n)
  | 0 => []
  | t + 1 =>
    let h := hist R₁ R₂ π₁ π₂ t
    h ++ [(R₁ (π₁ h), R₂ (π₂ h))]

/-- Player 1's forecast (of player 2) in round `t`. -/
def forecast₁ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin n → ℝ :=
  π₁ (hist R₁ R₂ π₁ π₂ t)

/-- Player 2's forecast (of player 1) in round `t`. -/
def forecast₂ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin m → ℝ :=
  π₂ (hist R₁ R₂ π₁ π₂ t)

/-- Player 1's play in round `t`: `R₁` of player 1's forecast. -/
def play₁ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin m :=
  R₁ (forecast₁ R₁ R₂ π₁ π₂ t)

/-- Player 2's play in round `t`: `R₂` of player 2's forecast. -/
def play₂ {m n : ℕ} (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ)
    (t : ℕ) : Fin n :=
  R₂ (forecast₂ R₁ R₂ π₁ π₂ t)

/-- `λ(G)`: the joint distributions `D` that are limit points of calibrated forecasts. There are
stationary deterministic best-reply functions `R₁, R₂` and history-dependent forecasting rules
`π₁, π₂` with values in the simplex, such that each player's forecasts are calibrated against the
other player's plays and the empirical joint distribution of play converges to `D`. -/
def LimitSet {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {D | ∃ (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
      (π₁ : List (Fin m × Fin n) → Fin n → ℝ) (π₂ : List (Fin m × Fin n) → Fin m → ℝ),
      IsBestReply₁ u₁ R₁ ∧ IsBestReply₂ u₂ R₂ ∧
      (∀ h, IsDist (π₁ h)) ∧ (∀ h, IsDist (π₂ h)) ∧
      Shared.Calibrated (forecast₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) ∧
      Shared.Calibrated (forecast₂ R₁ R₂ π₁ π₂) (play₁ R₁ R₂ π₁ π₂) ∧
      ∀ a b, Tendsto (fun t => empDist (play₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) t a b)
        atTop (𝓝 (D a b))}

end CalibratedCE.Generic
