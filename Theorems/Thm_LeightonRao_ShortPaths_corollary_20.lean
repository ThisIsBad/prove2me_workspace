import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- Corollary 20, p. 808. -/
theorem corollary_20 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hW : 0 < totalWeight N d)
    (hWS : totalWeight N d ≤ minCut N /
      (36 * Real.logb 2 (Fintype.card V : ℝ))) :
    ∃ T : Finset V,
      2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ) ∧
      HasRadii N d T
        (totalCap N / (2 * totalWeight N d * (Fintype.card V : ℝ) ^ 2))
        (1 / (2 * (Fintype.card V : ℝ) ^ 2)) := by sorry

end LeightonRao.ShortPaths

