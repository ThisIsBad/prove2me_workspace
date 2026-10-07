import Definitions.Def_KallenbergLP_Bias_Policy

open Filter

namespace KallenbergLP.Bias

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- Expected reward in period `n + 1`, for any history-dependent randomized policy. -/
def periodReward (M : MDP N α) (R : Policy M) (i : Fin N) (n : ℕ) : ℝ :=
  ∑ j : Fin N, ∑ a : α, occupancy M R i j a n * M.reward j a

/-- The discounted expected reward of a general policy. Used near `β = 1` from below. -/
noncomputable def discountedReward (M : MDP N α) (R : Policy M)
    (i : Fin N) (β : ℝ) : ℝ :=
  ∑' n : ℕ, β ^ n * periodReward M R i n

/-- The statewise supremum of discounted rewards over the entire policy class C. -/
noncomputable def optimalDiscounted (M : MDP N α) (i : Fin N) (β : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ R : Policy M, x = discountedReward M R i β}

/-- The average reward is the liminf of the finite-horizon average, as on p. 22. -/
noncomputable def averageReward (M : MDP N α) (R : Policy M) (i : Fin N) : ℝ :=
  liminf (fun T : ℕ => (T : ℝ)⁻¹ *
    ∑ n ∈ Finset.range T, periodReward M R i n) atTop

/-- The upper average reward of (4.2.9). -/
noncomputable def upperAverageReward (M : MDP N α) (R : Policy M) (i : Fin N) : ℝ :=
  limsup (fun T : ℕ => (T : ℝ)⁻¹ *
    ∑ n ∈ Finset.range T, periodReward M R i n) atTop

/-- The statewise supremum of average rewards over the entire policy class C. -/
noncomputable def optimalAverage (M : MDP N α) (i : Fin N) : ℝ :=
  sSup {x : ℝ | ∃ R : Policy M, x = averageReward M R i}

/-- Bias optimality on p. 22 compares with all policies, not only C_D. -/
def IsBiasOptimal (M : MDP N α) (R : Policy M) : Prop :=
  ∀ i : Fin N,
    Tendsto (fun β : ℝ => discountedReward M R i β - optimalDiscounted M i β)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 0)

/-- Average optimality is componentwise for every initial state. -/
def IsAverageOptimal (M : MDP N α) (R : Policy M) : Prop :=
  ∀ i : Fin N, averageReward M R i = optimalAverage M i

end KallenbergLP.Bias
