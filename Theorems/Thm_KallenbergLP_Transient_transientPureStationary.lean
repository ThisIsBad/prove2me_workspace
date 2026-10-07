import Definitions.Def_KallenbergLP_Transient_Policy
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Theorem 3.2.3: if some policy is transient, some pure stationary policy is transient. -/
theorem transientPureStationary
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α)
    (h : ∃ R : Policy M, IsTransient M R) :
    ∃ f : PureRule M, IsTransient M (purePolicy M f) := by sorry

end KallenbergLP.Transient

