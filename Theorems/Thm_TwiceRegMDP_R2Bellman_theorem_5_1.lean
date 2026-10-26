import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_R2Bellman_MDP
import Definitions.Def_TwiceRegMDP_R2Bellman_R2Ops

namespace TwiceRegMDP.R2Bellman

/-- Theorem 5.1, R² optimal policy (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 8; proof App. C.2,
p. 24). Under Assumption 5.1 (with witnesses `ϵ`; the proof assumes it):
1. `T^{∗,R²}` has a unique fixed point `v^{∗,R²}` (Definition 5.2 (ii) is well posed);
2. for every policy `π`, `T^{π,R²}` has a unique fixed point `v^{π,R²}` (Definition 5.2 (i));
3. a greedy policy for `v^{∗,R²}` exists; every greedy policy `π^∗` has `v^{π^∗,R²} = v^{∗,R²}`;
   every policy has `v^{π,R²} ≤ v^{∗,R²}`; and every policy whose R² value equals `v^{∗,R²}`
   (i.e. every optimal policy) is greedy for `v^{∗,R²}`;
4. if moreover `α^r_s > 0` for every `s`, the greedy policy for `v^{∗,R²}` is unique, so it is the
   unique optimal R² policy. -/
theorem theorem_5_1 {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (P₀ : S → A → S → ℝ) (hP₀ : FoundationsML.ReinforcementLearning.IsTransitionKernel P₀)
    (r₀ : S → A → ℝ)
    (αr αP : S → ℝ) (hαr : ∀ s, 0 ≤ αr s) (hαP : ∀ s, 0 ≤ αP s)
    (ϵ : S → ℝ) (hasm : BoundedRadius γ P₀ αP ϵ) :
    ∃ vstar : S → ℝ,
      optOpR2 γ P₀ r₀ αr αP vstar = vstar ∧
      (∀ v : S → ℝ, optOpR2 γ P₀ r₀ αr αP v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π → ∃! v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v) ∧
      (∃ π : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      (∀ πstar : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar πstar →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP πstar v = v → v = vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        ∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v ≤ vstar) ∧
      (∀ π : S → A → ℝ, TwiceRegMDP.RobustReg.IsPolicy π →
        (∀ v : S → ℝ, evalOpR2 γ P₀ r₀ αr αP π v = v → v = vstar) →
        IsGreedy γ P₀ r₀ αr αP vstar π) ∧
      ((∀ s, 0 < αr s) →
        ∀ π₁ π₂ : S → A → ℝ, IsGreedy γ P₀ r₀ αr αP vstar π₁ →
          IsGreedy γ P₀ r₀ αr αP vstar π₂ → π₁ = π₂) := by sorry

end TwiceRegMDP.R2Bellman

