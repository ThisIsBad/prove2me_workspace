import Mathlib
import Definitions.Def_FoundationsRL_Contextual_IsIGW
import Definitions.Def_FoundationsRL_Contextual_OracleGuarantee
import Definitions.Def_FoundationsRL_Contextual_regret


namespace FoundationsRL.Contextual

/-- Proposition 10 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, p. 51): SquareCB's regret bound. Given a context
sequence `x : Fin T → X`, ground-truth reward function `fstar` with optimal policy `pistar`,
an online regression oracle producing estimates `fhat` with cumulative squared-error
guarantee `EstSq` (`OracleGuarantee`), and SquareCB's realized action distributions
`p t = IGW_γ(fhat t (x t))` with `γ = √(TA / EstSq)`, the regret is at most
`2√(A T EstSq)` (the book's `≲ √(AT · EstSq(F,T,δ))`, with the exact constant `2` that the
proof establishes by balancing `TA/γ` against `γ · EstSq`). -/
theorem squarecb_regret_bound {X : Type*} {A T : ℕ} (hT : 0 < T)
    (x : Fin T → X) (fstar : X → Fin A → ℝ) (pistar : X → Fin A)
    (hpistar : ∀ (x' : X) (π : Fin A), fstar x' π ≤ fstar x' (pistar x'))
    (fhat : Fin T → X → Fin A → ℝ) (bstar : Fin T → Fin A)
    (EstSq : ℝ) (hEstSq : 0 < EstSq)
    (γ : ℝ) (hγ : γ = Real.sqrt ((T : ℝ) * A / EstSq))
    (p : Fin T → Fin A → ℝ) (hp : ∀ t, IsIGW A (fhat t (x t)) γ (bstar t) (p t))
    (hOracle : OracleGuarantee A T x fhat fstar p EstSq) :
    regret A T x fstar pistar p ≤ 2 * Real.sqrt ((A : ℝ) * T * EstSq) := by sorry

end FoundationsRL.Contextual

