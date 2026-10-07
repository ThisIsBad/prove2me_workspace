import Mathlib
import Definitions.Def_BellmanDP_GoldMining_MultiOutcome

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 4, p. 70: `n ≥ 1` mines, `K` outcomes per use.
Under (5): `p_ik ≥ 0`, `Σ_k p_ik < 1` for each `i`, `0 ≤ c_ik ≤ 1`, `c_ik + c'_ik = 1`, the
equation (4) has a solution bounded on every box `0 ≤ x_i ≤ X̄_i`, unique there on the orthant,
and at every state `x ≥ 0` any index `i` maximizing the decision function
`D_i(x) = (Σ_k p_ik c_ik) x_i / (1 − Σ_k p_ik)` attains the maximum in (4) (in case of equality
among maximizers, any of them may be used). -/
theorem index_rule_n_mines (n K : ℕ) (hn : 0 < n) (p c c' : Fin n → Fin K → ℝ)
    (hp : ∀ i k, 0 ≤ p i k) (hps : ∀ i, ∑ k, p i k < 1)
    (hc0 : ∀ i k, 0 ≤ c i k) (hc1 : ∀ i k, c i k ≤ 1) (hc' : ∀ i k, c i k + c' i k = 1) :
    ∃ f : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' f ∧ BoundedOnBoxes f ∧
      (∀ g : (Fin n → ℝ) → ℝ, IsNMineSolution p c c' g → BoundedOnBoxes g →
        ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → g x = f x) ∧
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → ∀ i : Fin n,
        (∀ j : Fin n, decisionFunction p c x j ≤ decisionFunction p c x i) →
          f x = mineOption p c c' f x i := by sorry

end BellmanDP.GoldMining

