import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

namespace TwiceRegMDP.RobustReg

/-- Theorem 4.1, general robust MDP (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 6). For the
s-rectangular uncertainty set `U = (P₀ + 𝒫) × (r₀ + ℛ)` around a nominal kernel `P₀` and reward
`r₀`, with every `𝒫_s ⊆ ℝ^{S×A}` and `ℛ_s ⊆ ℝ^A` nonempty and compact and every perturbed
transition `P₀(·|s,a) + P_s(·, a)` a probability distribution, and any policy `π`, the robust
operator `T^{π,U}` has a unique fixed point `v^{π,U}`, and it is the optimal solution of
`max ⟨v, μ₀⟩ s.t. v(s) ≤ T^π_{(P₀,r₀)} v(s) − σ_{ℛ_s}(−π_s) − σ_{𝒫_s}(−γ v · π_s) for all s`,
where `[v · π_s](s', a) = v(s') π_s(a)`. -/
theorem theorem_4_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (Pset : S → Set (S × A → ℝ)) (hPne : ∀ s, (Pset s).Nonempty) (hPc : ∀ s, IsCompact (Pset s))
    (hPker : ∀ s, ∀ Pp ∈ Pset s, ∀ a : A, (fun s' => P₀ s a s' + Pp (s', a)) ∈ stdSimplex ℝ S)
    (Rset : S → Set (A → ℝ)) (hRne : ∀ s, (Rset s).Nonempty) (hRc : ∀ s, IsCompact (Rset s))
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (rectUncertainty P₀ r₀ Pset Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (rectUncertainty P₀ r₀ Pset Rset) π v = v →
      IsOptimalSolution μ₀
        {w : S → ℝ | ∀ s, w s ≤ evalOp γ P₀ r₀ π w s - supportFn (Rset s) (-(π s))
            - supportFn (Pset s) (-(γ • vDotPi w π s))} v := by sorry

end TwiceRegMDP.RobustReg

