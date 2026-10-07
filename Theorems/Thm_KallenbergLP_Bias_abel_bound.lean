import Definitions.Def_KallenbergLP_Bias_Criteria

open Filter

namespace KallenbergLP.Bias

/-- Lemma 5.2.1 (p. 162): upper average reward bounds the Abel limsup. -/
theorem abel_bound {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (R : Policy M) (i : Fin N) :
    limsup (fun β : ℝ => (1 - β) * discountedReward M R i β)
      (nhdsWithin 1 (Set.Iio 1)) ≤ upperAverageReward M R i := by sorry

end KallenbergLP.Bias

