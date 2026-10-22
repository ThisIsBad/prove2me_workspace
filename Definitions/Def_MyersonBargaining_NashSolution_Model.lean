import Mathlib

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Equation (4): the marginal probability of player `i` having type `a`. -/
noncomputable def marginal (P : (∀ i, A i) → ℝ) (i : ι) (a : A i) : ℝ :=
  ∑ β ∈ Finset.univ.filter (fun β => β i = a), P β

/-- Equation (3): the conditional probability of profile `α` given player `i`'s type `a`. -/
noncomputable def cond (P : (∀ i, A i) → ℝ) (i : ι) (α : ∀ i, A i) (a : A i) : ℝ :=
  if α i = a then P α / marginal P i a else 0

/-- Equation (1), with the positive marginals required for equation (3). -/
structure Problem (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : ι → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] (C : Type) [Fintype C] [DecidableEq C] [Nonempty C] where
  U : ι → C → (∀ i, A i) → ℝ
  P : (∀ i, A i) → ℝ
  P_nonneg : ∀ α, 0 ≤ P α
  P_sum : ∑ α, P α = 1
  marginal_pos : ∀ i (a : A i), 0 < marginal P i a

/-- Equation (2): a lottery on `C` for every response profile. -/
def IsChoiceMechanism {S : ι → Type} [∀ i, Fintype (S i)]
    (π : C → (∀ i, S i) → ℝ) : Prop :=
  (∀ c s, 0 ≤ π c s) ∧ ∀ s, ∑ c, π c s = 1

/-- Equation (5): expected utility when player `i`, truly of type `a`, reports `b`. -/
noncomputable def Z (G : Problem ι A C) (i : ι)
    (π : C → (∀ i, A i) → ℝ) (b a : A i) : ℝ :=
  ∑ α, ∑ c, cond G.P i α a * π c (Function.update α i b) * G.U i c α

/-- Equation (6): no player type gains from a unilateral false report. -/
def IsBIC (G : Problem ι A C) (π : C → (∀ i, A i) → ℝ) : Prop :=
  ∀ i (a b : A i), Z G i π b a ≤ Z G i π a a

/-- Equations (7)–(8): the interim payoff vector indexed by player and type. -/
noncomputable def V (G : Problem ι A C) (π : C → (∀ i, A i) → ℝ) :
    (Σ i, A i) → ℝ :=
  fun x => Z G x.1 π x.2 x.2

/-- Equation (9): interim payoffs attained by direct choice mechanisms. -/
def F (G : Problem ι A C) : Set ((Σ i, A i) → ℝ) :=
  {x | ∃ π : C → (∀ i, A i) → ℝ, IsChoiceMechanism π ∧ V G π = x}

/-- Equation (10): interim payoffs attained by Bayesian incentive-compatible mechanisms. -/
def FStar (G : Problem ι A C) : Set ((Σ i, A i) → ℝ) :=
  {x | ∃ π : C → (∀ i, A i) → ℝ,
    IsChoiceMechanism π ∧ IsBIC G π ∧ V G π = x}

end MyersonBargaining.NashSolution
