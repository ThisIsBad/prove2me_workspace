import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

namespace TwiceRegMDP.RobustReg

/-- Proposition 3.1 (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 5). For a robust MDP with
uncertainty set `U := 𝒫 × ℛ` (p. 4), `𝒫` a nonempty compact set of transition kernels and `ℛ` a
nonempty compact set of rewards (not necessarily rectangular), and any policy `π`, the robust
operator `T^{π,U}` has a unique fixed point `v^{π,U}` (the robust value function), and it is the
optimal solution of `(P_U)`: `max ⟨v, μ₀⟩ s.t. v ≤ T^π_{(P,r)} v for all (P, r) ∈ U`. -/
theorem proposition_3_1 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (Pset : Set (S → A → S → ℝ)) (hPne : Pset.Nonempty) (hPc : IsCompact Pset)
    (hPker : ∀ P ∈ Pset, FoundationsML.ReinforcementLearning.IsTransitionKernel P)
    (Rset : Set (S → A → ℝ)) (hRne : Rset.Nonempty) (hRc : IsCompact Rset)
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v →
      IsOptimalSolution μ₀ {w : S → ℝ | ∀ m ∈ Pset ×ˢ Rset, w ≤ evalOp γ m.1 m.2 π w} v := by sorry

end TwiceRegMDP.RobustReg

