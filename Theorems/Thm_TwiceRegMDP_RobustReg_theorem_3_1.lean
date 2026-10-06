import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

namespace TwiceRegMDP.RobustReg

/-- Theorem 3.1, reward-robust MDP (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 5). For
`U = {P₀} × (r₀ + ℛ)` with `ℛ = ×_s ℛ_s`, each `ℛ_s` nonempty and compact, `P₀` a kernel, and any
policy `π`, the robust operator `T^{π,U}` has a unique fixed point `v^{π,U}`, and it is the optimal
solution of `max ⟨v, μ₀⟩ s.t. v(s) ≤ T^π_{(P₀,r₀)} v(s) − σ_{ℛ_s}(−π_s) for all s`. -/
theorem theorem_3_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (Rset : S → Set (A → ℝ)) (hRne : ∀ s, (Rset s).Nonempty) (hRc : ∀ s, IsCompact (Rset s))
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (rewardUncertainty P₀ r₀ Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (rewardUncertainty P₀ r₀ Rset) π v = v →
      IsOptimalSolution μ₀
        {w : S → ℝ | ∀ s, w s ≤ evalOp γ P₀ r₀ π w s - supportFn (Rset s) (-(π s))} v := by sorry

end TwiceRegMDP.RobustReg

