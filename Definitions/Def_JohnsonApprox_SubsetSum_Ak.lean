import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem

namespace JohnsonApprox.SubsetSum

variable {α : Type}

/-- The big elements `{x ∈ T : s(x) > b/(k + 1)}` of the input (strict inequality). -/
def bigElems (k : ℕ) (u : Input α) : Finset α :=
  u.T.filter (fun x => u.b / ((k : ℚ) + 1) < u.s x)

/-- The big part `X^BIG = {x ∈ X : s(x) > b/(k + 1)}` of a set `X`. -/
def bigPart (k : ℕ) (u : Input α) (X : Finset α) : Finset α :=
  X.filter (fun x => u.b / ((k : ℚ) + 1) < u.s x)

/-- Step 1 of `A_k`: `S` is a subset of the big elements "whose measure is closest to, without
exceeding `b`", i.e. of maximum measure among the subsets of big elements with measure `≤ b`.
Every such maximizer may be chosen (ties are allowed). -/
def IsStep1Choice (k : ℕ) (u : Input α) (S : Finset α) : Prop :=
  S ⊆ bigElems k u ∧ measure u S ≤ u.b ∧
    ∀ S' ⊆ bigElems k u, measure u S' ≤ u.b → measure u S' ≤ measure u S

/-- The state of algorithm `A_k`: the paper's variables `SUB`, `LEFT` and `SUM`. -/
structure State (α : Type) where
  SUB : Finset α
  LEFT : Finset α
  SUM : ℚ

/-- The state after Step 1 with the chosen set `S`: `SUB = S`, `SUM = m(S)`, `LEFT = T − SUB`. -/
def initState [DecidableEq α] (u : Input α) (S : Finset α) : State α :=
  ⟨S, u.T \ S, measure u S⟩

/-- The halting test of Step 2: for all `x ∈ LEFT`, `s(x) + SUM > b`. -/
def Halts (u : Input α) (σ : State α) : Prop :=
  ∀ x ∈ σ.LEFT, u.b < u.s x + σ.SUM

/-- One pass through Steps 2–4 of `A_k`: Step 2 does not halt, Step 3 picks any `y ∈ LEFT` for
which `s(y) + SUM` is closest to, without exceeding, `b` (ties allowed), and Step 4 moves `y`
from `LEFT` to `SUB` and adds `s(y)` to `SUM`. -/
def Step [DecidableEq α] (u : Input α) (σ σ' : State α) : Prop :=
  ¬ Halts u σ ∧
    ∃ y ∈ σ.LEFT, u.s y + σ.SUM ≤ u.b ∧
      (∀ z ∈ σ.LEFT, u.s z + σ.SUM ≤ u.b → u.s z + σ.SUM ≤ u.s y + σ.SUM) ∧
      σ' = ⟨σ.SUB ∪ {y}, σ.LEFT.erase y, σ.SUM + u.s y⟩

/-- `T₁` is choosable by `A_k` on input `u`: for some admissible Step 1 choice, some finite
sequence of admissible iterations of Steps 2–4 reaches a state at which Step 2 halts, and the
returned set `SUB` is `T₁`. -/
def Choosable [DecidableEq α] (k : ℕ) (u : Input α) (T₁ : Finset α) : Prop :=
  ∃ S, IsStep1Choice k u S ∧
    ∃ σ, Relation.ReflTransGen (Step u) (initState u S) σ ∧ Halts u σ ∧ σ.SUB = T₁

end JohnsonApprox.SubsetSum
