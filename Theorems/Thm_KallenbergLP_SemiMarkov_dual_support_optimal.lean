import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Fintype U] [Nonempty S] [DecidableEq S] [DecidableEq U]

/-- Theorem 7.2.3. Every pure stationary action choice supported positively
by an optimal dual solution is an optimal policy. -/
theorem dual_support_optimal (M : Discounted S U) (β : S → ℝ)
    (hβ : ∀ i, 0 < β i) (x : S → U → ℝ) (hx : DualOptimal M β x)
    (f : S → U) (hf : ∀ i, f i ∈ M.model.actions i)
    (hpositive : ∀ i, 0 < x i (f i)) :
    ∀ i, policyValue M (purePolicy M f hf) i = value M i := by sorry

end KallenbergLP.SemiMarkov

