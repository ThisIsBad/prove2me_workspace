import Mathlib
import Definitions.Def_KallenbergLP_SemiMarkov_Discounted

namespace KallenbergLP.SemiMarkov

variable {S U : Type*} [Fintype S] [Nonempty S] [Fintype U] [DecidableEq S] [DecidableEq U]

/-- Lemma 7.2.1. `discountedVisit` is the Laplace–Stieltjes integral of the
book's arrival-time distribution `π_{iaj}(n,t,R)`, with Lean epoch `n=0`
corresponding to printed epoch `n=1`. -/
theorem reward_occupation_identity (M : Discounted S U) (R : Policy M) (i : S) :
    policyValue M R i =
      ∑' n : ℕ, ∑ j : S, ∑ a ∈ M.model.actions j,
        rStar M j a * discountedVisit M R n [] i j a := by sorry

end KallenbergLP.SemiMarkov

