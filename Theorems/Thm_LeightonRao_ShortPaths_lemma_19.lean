import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- Lemma 19, p. 808. The positivity of W makes the paper's radius ΔC/W meaningful. -/
theorem lemma_19 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (Δ : ℝ) (hΔ : 0 < Δ) (hW : 0 < totalWeight N d) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, HasRadii N d S (Δ * totalCap N / totalWeight N d) Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d *
        Real.logb 2 (Fintype.card V : ℝ) / Δ := by sorry

end LeightonRao.ShortPaths

