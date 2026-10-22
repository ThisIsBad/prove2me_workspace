import Mathlib

namespace OceanicGames.Limit

/-- The finite weighted majority game of Appendix (A.4), with a coalition winning
when its total weight is at least the quota. -/
noncomputable def wmGame {N : ℕ} (c : ℝ) (u : Fin N → ℝ) : Finset (Fin N) → ℝ :=
  fun S => if c ≤ ∑ j ∈ S, u j then 1 else 0

end OceanicGames.Limit
