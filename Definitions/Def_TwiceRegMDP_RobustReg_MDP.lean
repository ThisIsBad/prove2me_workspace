import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition

namespace TwiceRegMDP.RobustReg

/-- A (stochastic, stationary) policy `π ∈ Δ_A^S` (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 3):
for every state `s`, `π s` is a probability distribution over the finite action set `A`. -/
def IsPolicy {S A : Type} [Fintype A] (π : S → A → ℝ) : Prop :=
  ∀ s : S, π s ∈ stdSimplex ℝ A

/-- The expected reward under `π`, `r^π(s) := ⟨π_s, r(s, ·)⟩` (p. 3). -/
def rewardPi {S A : Type} [Fintype A] (π : S → A → ℝ) (r : S → A → ℝ) : S → ℝ :=
  fun s => ∑ a, π s a * r s a

/-- The policy transition operator applied to `v`:
`(P^π v)(s) := ∑_{s'} P^π(s'|s) v(s')` with `P^π(s'|s) := ⟨π_s, P(s'|s, ·)⟩` (p. 3), where
`P^π(s'|s)` is the published `InducedTransition π P s s' = ∑_a π s a * P s a s'`.
Here `P s a s'` is `P(s'|s, a)`; `P` is an arbitrary array, not necessarily a kernel. -/
noncomputable def transPi {S A : Type} [Fintype S] [Fintype A] (π : S → A → ℝ)
    (P : S → A → S → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => ∑ s', FoundationsML.ReinforcementLearning.InducedTransition π P s s' * v s'

/-- The evaluation Bellman operator `T^π_{(P,r)} v := r^π + γ P^π v` (p. 3). -/
noncomputable def evalOp {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (P : S → A → S → ℝ)
    (r : S → A → ℝ) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => rewardPi π r s + γ * transPi π P v s

/-- The inner product `⟨v, μ⟩ := ∑_s v(s) μ(s)` on `ℝ^S` (p. 2). -/
def pairing {S : Type} [Fintype S] (v μ : S → ℝ) : ℝ :=
  ∑ s, v s * μ s

/-- The support function `σ_C(y) := max_{a ∈ C} ⟨a, y⟩` of a set `C ⊆ ℝ^ι` (p. 2), written as the
real `sSup` of `{⟨a, y⟩ : a ∈ C}`. This is the true maximum when `C` is nonempty and compact; every
use in this mission is under that hypothesis (on an empty or unbounded set the real `sSup` is `0`). -/
noncomputable def supportFn {ι : Type} [Fintype ι] (C : Set (ι → ℝ)) (y : ι → ℝ) : ℝ :=
  sSup ((fun a : ι → ℝ => ∑ i, a i * y i) '' C)

/-- `v` is *the* optimal solution of `max_{w ∈ ℝ^S} ⟨w, μ₀⟩ s.t. w ∈ F`: it is feasible, no feasible
point has a larger objective, and it is the only feasible point attaining the optimal objective. -/
def IsOptimalSolution {S : Type} [Fintype S] (μ₀ : S → ℝ) (F : Set (S → ℝ)) (v : S → ℝ) : Prop :=
  v ∈ F ∧ (∀ w ∈ F, pairing w μ₀ ≤ pairing v μ₀) ∧
    (∀ w ∈ F, pairing w μ₀ = pairing v μ₀ → w = v)

end TwiceRegMDP.RobustReg
