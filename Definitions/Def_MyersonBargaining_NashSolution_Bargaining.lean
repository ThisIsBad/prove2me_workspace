import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Model

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Equation (11): every player type gets a strictly larger interim payoff. -/
def StrictlyDominates (x y : (Σ i, A i) → ℝ) : Prop :=
  ∀ k, y k < x k

/-- Section 4: incentive-compatible and not strictly dominated by another such mechanism. -/
def IsIncentiveEfficient (G : Problem ι A C)
    (π : C → (∀ i, A i) → ℝ) : Prop :=
  IsChoiceMechanism π ∧ IsBIC G π ∧
    ¬ ∃ π' : C → (∀ i, A i) → ℝ,
      IsChoiceMechanism π' ∧ IsBIC G π' ∧ StrictlyDominates (V G π') (V G π)

/-- The mechanism which always selects the conflict choice `cstar`. -/
def constMech (cstar : C) : C → (∀ i, A i) → ℝ :=
  fun c _ => if c = cstar then 1 else 0

/-- Equation (16): interim utility at the conflict outcome. -/
noncomputable def conflictPayoff (G : Problem ι A C) (cstar : C) :
    (Σ i, A i) → ℝ :=
  fun k => ∑ α, cond G.P k.1 α k.2 * G.U k.1 cstar α

/-- Equation (17): incentive-feasible vectors at least as good as conflict for every type. -/
def FPlus (G : Problem ι A C) (cstar : C) : Set ((Σ i, A i) → ℝ) :=
  FStar G ∩ {y | ∀ k, conflictPayoff G cstar k ≤ y k}

/-- Equation (18): the generalized Nash product, weighted by marginal type probabilities. -/
noncomputable def nashProduct (G : Problem ι A C) (cstar : C)
    (x : (Σ i, A i) → ℝ) : ℝ :=
  ∏ i, ∏ a : A i,
    (x ⟨i, a⟩ - conflictPayoff G cstar ⟨i, a⟩) ^ (marginal G.P i a)

/-- Section 5: a maximizer of (18) over the set (17). -/
def IsBargainingSolution (G : Problem ι A C) (cstar : C)
    (x : (Σ i, A i) → ℝ) : Prop :=
  x ∈ FPlus G cstar ∧
    ∀ y ∈ FPlus G cstar, nashProduct G cstar y ≤ nashProduct G cstar x

end MyersonBargaining.NashSolution
