import Mathlib
import Definitions.Def_BellmanDP_GoldMining_Model
import Definitions.Def_BellmanDP_GoldMining_MultiOutcome

namespace BellmanDP.GoldMining

/-- Bellman, *Dynamic Programming*, Ch. II, Theorem 3, pp. 69–70: two mines, `K` outcomes per use
(the book's `N`). Under (2): `p_k, q_k ≥ 0`, `Σ p_k < 1`, `Σ q_k < 1`, `0 ≤ c_k, d_k ≤ 1`,
`c'_k + c_k = d'_k + d_k = 1`, the solution `f` of (1) (bounded in every rectangle) satisfies at
every `x, y ≥ 0`: `f = A` if `(Σ p_k c_k)/(1 − Σ p_k) x > (Σ q_k d_k)/(1 − Σ q_k) y`, `f = B` if
the reverse holds, and `f = A = B` on equality. -/
theorem index_rule_multi_outcome (K : ℕ) (p c c' q d d' : Fin K → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hps : ∑ k, p k < 1) (hqs : ∑ k, q k < 1)
    (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1) (hd0 : ∀ k, 0 ≤ d k) (hd1 : ∀ k, d k ≤ 1)
    (hc' : ∀ k, c' k + c k = 1) (hd' : ∀ k, d' k + d k = 1)
    (f : ℝ → ℝ → ℝ) (hf : IsTwoMineSolution K p c c' q d d' f) (hfb : BoundedOnRectangles f)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((∑ k, q k * d k) / (1 - ∑ k, q k) * y < (∑ k, p k * c k) / (1 - ∑ k, p k) * x →
        f x y = optA K p c c' f x y) ∧
    ((∑ k, p k * c k) / (1 - ∑ k, p k) * x < (∑ k, q k * d k) / (1 - ∑ k, q k) * y →
        f x y = optB K q d d' f x y) ∧
    ((∑ k, p k * c k) / (1 - ∑ k, p k) * x = (∑ k, q k * d k) / (1 - ∑ k, q k) * y →
        f x y = optA K p c c' f x y ∧ f x y = optB K q d d' f x y) := by sorry

end BellmanDP.GoldMining

