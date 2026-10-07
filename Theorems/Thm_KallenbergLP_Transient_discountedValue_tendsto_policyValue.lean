import Definitions.Def_KallenbergLP_Transient_TotalReward
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Lemma 3.2.1: under Assumption 3.2.1, `lim_{δ ↑ 1} v^δ_i(R) = v_i(R)` in `[-∞, +∞]`. -/
theorem discountedValue_tendsto_policyValue
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (r : Fin N → α → ℝ)
    (hreward : TotalRewardExists M r) (i : Fin N) (R : Policy M) :
    Filter.Tendsto (fun δ : ℝ => (discountedValue M r R i δ : EReal))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (policyValue M r R i)) := by sorry

end KallenbergLP.Transient

