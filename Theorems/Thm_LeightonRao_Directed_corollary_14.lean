import Mathlib
import Definitions.Def_LeightonRao_Directed_Setting

namespace LeightonRao.Directed

/-- Leighton–Rao, Corollary 14, p. 806. With `Δ = 1/(4n²)`, either some node `v` has
`|𝒩^Δ_in(v)| ≥ 2n/3` and `|𝒩^Δ_out(v)| ≥ 2n/3`, or some directed cut has ratio cost at most
`8 W log₂ n / (Δ (n/6)(5n/6))` (the bound computed in the proof, `= (1152/5) W log₂ n`). -/
theorem corollary_14 {V : Type} [Fintype V] [DecidableEq V] (N : DiNetwork V)
    (hn : 2 ≤ Fintype.card V) (d : V → V → ℝ) (hd : ∀ u v, 0 ≤ d u v) :
    let n : ℝ := (Fintype.card V : ℝ)
    let Δ : ℝ := 1 / (4 * n ^ 2)
    (∃ v, 2 * n ≤ 3 * ((inBall N d v Δ).card : ℝ) ∧
        2 * n ≤ 3 * ((outBall N d v Δ).card : ℝ)) ∨
    (∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
        diRatio N U ≤ 8 * diTotalWeight N d * Real.logb 2 n / (Δ * (n / 6) * (5 * n / 6))) := by sorry

end LeightonRao.Directed

