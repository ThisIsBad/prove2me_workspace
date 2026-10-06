import Mathlib
import Definitions.Def_TwiceRegMDP_RobustReg_MDP

namespace TwiceRegMDP.RobustReg

/-- The robust Bellman evaluation operator of an uncertainty set `U` of models `(P, r)`
(Derman–Geist–Mannor, arXiv:2110.06267v1, p. 4):
`[T^{π,U} v](s) := min_{(P,r) ∈ U} T^π_{(P,r)} v(s)`, written as the real `sInf` of the values.
It is the true minimum when `U` is nonempty and compact, which every theorem using it assumes. -/
noncomputable def robustOp {S A : Type} [Fintype S] [Fintype A] (γ : ℝ)
    (U : Set ((S → A → S → ℝ) × (S → A → ℝ))) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => sInf ((fun m : (S → A → S → ℝ) × (S → A → ℝ) => evalOp γ m.1 m.2 π v s) '' U)

/-- The s-rectangular uncertainty set `U = (P₀ + 𝒫) × (r₀ + ℛ)` around a nominal model `(P₀, r₀)`
(pp. 4–5), with `𝒫 = ×_s 𝒫_s` and `ℛ = ×_s ℛ_s`. The perturbation `P_s ∈ 𝒫_s ⊆ ℝ^{S×A}` of the
transition block at `s` is indexed as in the paper, `P_s(s', a)`, and is added to `P₀(s'|s, a)`;
the reward perturbation `r_s ∈ ℛ_s ⊆ ℝ^A` is added to `r₀(s, ·)`. -/
def rectUncertainty {S A : Type} (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ)
    (Pset : S → Set (S × A → ℝ)) (Rset : S → Set (A → ℝ)) :
    Set ((S → A → S → ℝ) × (S → A → ℝ)) :=
  {m | ∃ (Pp : S → S × A → ℝ) (rp : S → A → ℝ), (∀ s, Pp s ∈ Pset s ∧ rp s ∈ Rset s) ∧
    m = (fun s a s' => P₀ s a s' + Pp s (s', a), fun s a => r₀ s a + rp s a)}

/-- The reward-robust uncertainty set `U = {P₀} × (r₀ + ℛ)` with `ℛ = ×_s ℛ_s` (p. 5): the
transition model is the nominal `P₀`, the reward is `r₀(s, ·) + r_s` with `r_s ∈ ℛ_s`. -/
def rewardUncertainty {S A : Type} (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ)
    (Rset : S → Set (A → ℝ)) : Set ((S → A → S → ℝ) × (S → A → ℝ)) :=
  {m | ∃ rp : S → A → ℝ, (∀ s, rp s ∈ Rset s) ∧ m = (P₀, fun s a => r₀ s a + rp s a)}

/-- The matrix `v · π_s ∈ ℝ^{S×A}`, `[v · π_s](s', a) := v(s') π_s(a)` (p. 6). -/
def vDotPi {S A : Type} (v : S → ℝ) (π : S → A → ℝ) (s : S) : S × A → ℝ :=
  fun x => v x.1 * π s x.2

end TwiceRegMDP.RobustReg
