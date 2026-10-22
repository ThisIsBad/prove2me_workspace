import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- Lemma 21, p. 809. The length `L` is real, as on the page; `d(T, u)` uses walks with at most
`L / 4` edges. The restricted distances are extended nonnegative reals. -/
theorem lemma_21 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (L : ℝ)
    (hL : 12 * cmax N * Real.log (Fintype.card V : ℝ) /
      ((Fintype.card V : ℝ) * minCut N) ≤ L)
    (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ)) :
    ∑ u ∈ Tᶜ, distFromL N d (L / 4) T u ≤
      ENNReal.ofReal (6 * totalWeight N d /
        ((Fintype.card V : ℝ) * minCut N)) := by sorry

end LeightonRao.ShortPaths

