import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP

namespace TwiceRegMDP.R2Bellman

open Finset

/-! Finite discounted MDP objects of Derman–Geist–Mannor (arXiv:2110.06267v1, pp. 2–3).
A transition array is `P : S → A → S → ℝ` with `P s a s'` = P(s'|s,a); being a kernel is the
separate hypothesis `FoundationsML.ReinforcementLearning.IsTransitionKernel P` (imported). -/

/-- The ℓ²-norm `‖a‖ = √⟨a, a⟩ = √(∑_z a(z)²)` of a real function on a finite set (p. 2).
Mathlib's own norm on `Z → ℝ` is the sup norm, which is *not* this one. -/
noncomputable def l2norm {Z : Type} [Fintype Z] (a : Z → ℝ) : ℝ :=
  Real.sqrt (∑ z, a z ^ 2)

/-- The q-function of `v`: `q(s,a) = r(s,a) + γ ⟨P(·|s,a), v⟩` (p. 3). -/
noncomputable def qfun {S A : Type} [Fintype S] (γ : ℝ) (P : S → A → S → ℝ)
    (r : S → A → ℝ) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  r s a + γ * ∑ s', P s a s' * v s'

/-- The evaluation Bellman operator `T^π_{(P,r)} v = r^π + γ P^π v` (p. 3):
`[T^π_{(P,r)} v](s) = ∑_a π_s(a) (r(s,a) + γ ∑_{s'} P(s'|s,a) v(s'))`. -/
noncomputable def evalOp {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (P : S → A → S → ℝ)
    (r : S → A → ℝ) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => ∑ a, π s a * qfun γ P r v s a

end TwiceRegMDP.R2Bellman
