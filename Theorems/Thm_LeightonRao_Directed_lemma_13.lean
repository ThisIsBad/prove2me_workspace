import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Lemma 13, p. 804. For any directed network, any `Δ > 0` and any nonnegative
distance function of total weight `W`, there is an ordered partition `V₁, …, V_r` of `V`
(`V_i = {x | lab x = i}`) such that
(1) the edges directed from a later part to an earlier part (`u ∈ V_i`, `v ∈ V_j`, `j < i ≤ r`) have
total capacity at most `8 W log₂ n / Δ`, and
(2) every part `V_i` contains a node `v` with `|𝒩^Δ_in(v)| ≥ |V_i|` and `|𝒩^Δ_out(v)| ≥ |V_i|`
(in particular every part is nonempty). -/
theorem lemma_13 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (r : ℕ) (lab : V → Fin r),
      (∑ u, ∑ v, if lab v < lab u then N.C u v else 0) ≤
        8 * diTotalWeight N d * Real.logb 2 (Fintype.card V) / Δ ∧
      ∀ i : Fin r, ∃ v, lab v = i ∧
        (Finset.univ.filter (fun x => lab x = i)).card ≤ (inBall N d v Δ).card ∧
        (Finset.univ.filter (fun x => lab x = i)).card ≤ (outBall N d v Δ).card := by sorry

end LeightonRao.Directed

