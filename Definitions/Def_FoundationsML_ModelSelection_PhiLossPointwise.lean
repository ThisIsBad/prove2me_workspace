import Mathlib

namespace FoundationsML.ModelSelection

/-- The pointwise Φ-loss `L_Φ(x, u) = η(x) Φ(−u) + (1 − η(x)) Φ(u)` at a point `x ∈ X` and a
score `u ∈ ℝ`, for a conditional label probability `η(x) = P[y = +1 | x]` and a convex
non-decreasing surrogate `Φ : ℝ → ℝ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 75, PDF p. 92). -/
def PhiLossPointwise {X : Type*} (η : X → ℝ) (Φ : ℝ → ℝ) (x : X) (u : ℝ) : ℝ :=
  η x * Φ (-u) + (1 - η x) * Φ u

end FoundationsML.ModelSelection
