import Definitions.Def_KallenbergLP_Positive_Dual

namespace KallenbergLP.Positive

/-- Theorem 3.5.2. Every admissible pure rule that selects a positive-flow
action on `E_x` is optimal among all policies, including nontransient ones. -/
theorem extreme_optimal_dual_yields_policy
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (β : Fin N → ℝ)
    (hr : ∀ i a, a ∈ M.actions i → 0 ≤ M.reward i a)
    (hβ : ∀ j, 0 < β j)
    (x : Flow M)
    (hx : IsDualOptimal M β x)
    (hext : x ∈ Set.extremePoints ℝ (dualFeasible M β)) :
    ∀ f : PureRule M,
      (∀ i, i ∈ occupiedStates M x →
        0 < x i ⟨f.choose i, f.admissible i⟩) →
      ∀ i : Fin N, totalReward M (purePolicy M f) i = value M i := by sorry

end KallenbergLP.Positive

