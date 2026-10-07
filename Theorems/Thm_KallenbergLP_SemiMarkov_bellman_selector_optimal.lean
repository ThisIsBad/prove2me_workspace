import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Fintype U] [Nonempty S] [DecidableEq S] [DecidableEq U]

/-- Theorem 7.2.2. Any pure stationary selector attaining the Bellman value
at every state is optimal among all history-dependent randomized policies. -/
theorem bellman_selector_optimal (M : Discounted S U) (f : S → U)
    (hf : ∀ i, f i ∈ M.model.actions i)
    (hbellman : ∀ i, rStar M i (f i) +
      ∑ j, pStar M i (f i) j * value M j = value M i) :
    ∀ i, policyValue M (purePolicy M f hf) i = value M i := by sorry

end KallenbergLP.SemiMarkov

