import Mathlib

namespace LeastSquaresTD.Absorbing

/-- The finite, row-stochastic transition matrix used after fixing a policy (§2, p. 35). -/
structure Chain (X : Type*) [Fintype X] where
  P : Matrix X X ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  row_sum : ∀ x, ∑ y, P x y = 1

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Kemeny–Snell's absorbing condition as used in Theorem 1: an absorbing state is
reachable from every state. The absorbing states are those with `P(x,x)=1`. -/
def Chain.IsAbsorbing (C : Chain X) : Prop :=
  ∀ x, ∃ (n : ℕ) (y : X), C.P y y = 1 ∧ 0 < (C.P ^ n) x y

/-- The non-absorbing states, denoted `𝒩` in Theorem 1. -/
def Chain.Nonabsorbing (C : Chain X) : Type _ := {x : X // C.P x x ≠ 1}

noncomputable instance (C : Chain X) : Fintype C.Nonabsorbing := by
  classical
  unfold Chain.Nonabsorbing
  infer_instance

noncomputable instance (C : Chain X) : DecidableEq C.Nonabsorbing := Classical.decEq _

/-- A start law has no inaccessible states: every state can be reached from its
positive support (Theorem 1, condition (1), p. 43). -/
def Chain.AllAccessible (C : Chain X) (S : X → ℝ) : Prop :=
  ∀ x, ∃ (s : X) (n : ℕ), 0 < S s ∧ 0 < (C.P ^ n) s x

/-- Table 1, p. 35: expected reward on leaving `x`. -/
def Chain.rbar (C : Chain X) (R : X → X → ℝ) (x : X) : ℝ :=
  ∑ y, C.P x y * R x y

/-- The expected discounted return (p. 34). The Markov property identifies
`(P^k rbar)(x)` with the expected reward at step `k` from `x`. The theorems
assert summability explicitly, including at `γ=1`. -/
noncomputable def Chain.value (C : Chain X) (R : X → X → ℝ) (γ : ℝ) (x : X) : ℝ :=
  ∑' k : ℕ, γ ^ k * (Matrix.mulVec (C.P ^ k) (C.rbar R)) x

/-- Figure 2, p. 42: advance with `P` from a non-absorbing state and draw
again from the start law when the current trial has ended. -/
noncomputable def Chain.restartKernel (C : Chain X) (S : X → ℝ) : Matrix X X ℝ :=
  fun x y => if C.P x x = 1 then S y else C.P x y

end LeastSquaresTD.Absorbing
