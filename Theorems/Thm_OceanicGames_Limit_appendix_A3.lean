import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset Filter Topology

/-- Appendix (A.1)–(A.3): the finite Shapley values converge to the
integral expression under vanishing maximum minor weight. -/
theorem appendix_A3 {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ)
    (n : ℕ → ℕ) (cl : ℕ → ℝ) (wl : ℕ → Fin m → ℝ)
    (a : (l : ℕ) → Fin (n l) → ℝ) (i : Fin m)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j)
    (hwl : ∀ l j, 0 ≤ wl l j) (ha : ∀ l j, 0 ≤ a l j)
    (hclim : Tendsto cl atTop (𝓝 c))
    (hwlim : ∀ j, Tendsto (fun l => wl l j) atTop (𝓝 (w j)))
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 alpha))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε) :
    Tendsto (fun l => finiteValue (cl l) (wl l) (a l) i)
      atTop (𝓝 (limitFormula c alpha w i)) := by sorry

end OceanicGames.Limit

