import Mathlib
import Definitions.Def_PathFindingLP_Centering_WeightFunction

open Matrix

namespace PathFindingLP.Centering

/-- Theorem 5 (Centering with Weights), §IV.C, p. 428: let `g` be a weight function for `A`
with constants `c₁, c_γ, c_r`, let `x_old ∈ S⁰` and
`x_new = x_old - (1/(1+c_r)) h_t(x_old, g(s(x_old)))` (eq. (5)). If
`δ_t(x_old, g(s(x_old))) ≤ 1/(100 c_γ c_r²)` then `x_new ∈ S⁰` and
`δ_t(x_new, g(s(x_new))) ≤ (1 - 1/(4 c_r)) δ_t(x_old, g(s(x_old)))`. -/
theorem centering_with_weights {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n)
    (g : (Fin m → ℝ) → (Fin m → ℝ)) (c₁ cγ cr : ℝ) (hg : IsWeightFunction A g c₁ cγ cr)
    (t : ℝ) (xOld : Fin n → ℝ) (hx : xOld ∈ interiorS0 A b)
    (hδ : centrality A b c t xOld (g (slack A b xOld)) ≤ 1 / (100 * cγ * cr ^ 2)) :
    let xNew := xOld - (1 / (1 + cr)) • newtonStep A b c t xOld (g (slack A b xOld))
    xNew ∈ interiorS0 A b ∧
      centrality A b c t xNew (g (slack A b xNew)) ≤
        (1 - 1 / (4 * cr)) * centrality A b c t xOld (g (slack A b xOld)) := by sorry

end PathFindingLP.Centering

