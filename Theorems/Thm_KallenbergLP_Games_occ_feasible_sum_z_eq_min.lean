import Mathlib
import Definitions.Def_KallenbergLP_Games_SingleController

namespace KallenbergLP.Games

/-- Theorem 6.2.4 (i) (p. 198): under Assumptions 6.2.1 and 6.2.2, with `β ≫ 0`, for every
stationary policy `π^∞` of player I, `(x(π), z(π))` is feasible for (6.2.2) and
`∑_i z_i(π) = min_ρ ∑_j β_j v_j(π^∞, ρ^∞)`, the minimum over stationary policies of player II. -/
theorem occ_feasible_sum_z_eq_min {N : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (G : Game N α β) (hA : Assumption621 G) (hC : Assumption622 G)
    (β' : Fin N → ℝ) (hβ : ∀ j, 0 < β' j)
    (π : Fin N → α → ℝ) (hπ : IsDecisionRule1 G π) :
    LP622Feasible G β' (occ G β' π) (zval G β' π) ∧
      IsLeast
        {c : ℝ | ∃ (ρ : Fin N → β → ℝ) (hρ : IsDecisionRule2 G ρ),
          c = ∑ j, β' j * totalReward G (stationary1 G π hπ) (stationary2 G ρ hρ) j}
        (∑ i, zval G β' π i) := by sorry

end KallenbergLP.Games

