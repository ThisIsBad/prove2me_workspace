import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

/-- Hoffman 1952, p. 263, Lemma 1. If `F_m` satisfies (3), there is `e > 0` such that for every
`y` and every subset `S` of the rows, `F_m(ȳ) ≤ e F_m(y)`, where `ȳ` keeps the coordinates of `y`
in `S` and replaces the others by `0`. -/
theorem lemma1 {m : ℕ} (Fm : (Fin m → ℝ) → ℝ) (hFm : IsPosHomogeneous Fm) :
    ∃ e : ℝ, 0 < e ∧ ∀ (y : Fin m → ℝ) (S : Finset (Fin m)), Fm (restrictVec S y) ≤ e * Fm y := by sorry

end HoffmanBound.ErrorBound

