import Definitions.Def_KallenbergLP_Transient_TotalReward
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.2: under Assumption 3.2.1, a p-summable TMD value vector solves the
extended-real functional equation `x_i = max_a {r_ia + ∑_j p_iaj x_j}`, `x` p-summable. -/
theorem valueVector_functionalEquation
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (r : Fin N → α → ℝ)
    (hreward : TotalRewardExists M r)
    (hv : PSummable M (valueVector M r)) :
    (∀ i : Fin N, valueVector M r i = bellmanRHS M r (valueVector M r) i) ∧
      PSummable M (valueVector M r) := by sorry

end KallenbergLP.Transient

