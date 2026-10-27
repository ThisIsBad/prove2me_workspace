import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

namespace ThresholdMNL.Pricing

/-- Theorem 1 (p. 13): some utility-net-cost ordered assortment `S_{n*}` is an optimal offer set
for problem (3), "optimal" read as attaining the optimal value `V`, the least upper bound of
`R(S, p; Δ)` over all offer sets and prices; when (3) has a maximizer, `S_{n*}` carries one. -/
theorem theorem_1 {N : ℕ} (hN : 1 ≤ N) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i) :
    ∃ V : ℝ,
      IsLUB {x | ∃ (S : Finset (Fin N)) (p : Fin N → ℝ), x = profit S α c β u0 Δ p} V ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        IsLUB {x | ∃ p : Fin N → ℝ, x = profit (ordAssort N n) α c β u0 Δ p} V ∧
        ((∃ (S : Finset (Fin N)) (p : Fin N → ℝ), profit S α c β u0 Δ p = V) →
          ∃ p : Fin N → ℝ, profit (ordAssort N n) α c β u0 Δ p = V) := by sorry

end ThresholdMNL.Pricing

