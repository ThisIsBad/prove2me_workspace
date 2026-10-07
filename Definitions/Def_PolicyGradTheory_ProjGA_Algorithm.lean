import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Projection

namespace PolicyGradTheory.ProjGA

open FoundationsML.ReinforcementLearning

/-- The direct parameterization (2) (arXiv:1908.00261v5, p. 10): a parameter vector
`π ∈ ℝ^{S × A}` read as the table `π(a|s) = π_{s,a}`. -/
def asPolicy {S A : Type*} (π : EuclideanSpace ℝ (S × A)) : S → A → ℝ :=
  fun s a => π (s, a)

/-- The product simplex `∆(A)^{|S|}` (p. 10): the parameter vectors whose table is a policy,
`π_{s,a} ≥ 0` and `∑_a π_{s,a} = 1` for every `s`. -/
def simplexSet (S A : Type*) [Fintype A] : Set (EuclideanSpace ℝ (S × A)) :=
  {π | IsPolicy (asPolicy π)}

/-- The objective `π ↦ V^π(μ)` of the direct parameterization, as a function on the whole
parameter space `ℝ^{S × A}` (it is the paper's `V^π(μ)` at points of `simplexSet`). Its
Euclidean gradient is the paper's `∇_π V^π(μ)`. -/
noncomputable def directValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ)
    (π : EuclideanSpace ℝ (S × A)) : ℝ :=
  valueAt (asPolicy π) P r γ μ

/-- A run of projected gradient ascent (9) (p. 15) on `V^π(μ)` with step size `η` and projection
`Proj`: `π^{(t+1)} = Proj(π^{(t)} + η ∇_π V^{(t)}(μ))` for every `t`. -/
def IsProjGARun {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ) (η : ℝ)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (π : ℕ → EuclideanSpace ℝ (S × A)) : Prop :=
  ∀ t : ℕ, π (t + 1) = Proj (π t + η • gradient (directValue P r γ μ) (π t))

end PolicyGradTheory.ProjGA
