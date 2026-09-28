import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem

namespace JohnsonApprox.SetCover

/-!
Algorithm C1 (Johnson 1974, p. 265):
1. Set SUB = ∅, UNCOV = ⋃_{S∈F} S, N = |F|, SET[i] = S_i, 1 ≤ i ≤ N.
2. If UNCOV = ∅, halt and return SUB.
3. Choose j ≤ N such that |SET[j]| is maximized.
4. Set SUB = SUB ∪ {S_j}, UNCOV = UNCOV − SET[j], SET[i] = SET[i] − SET[j], 1 ≤ i ≤ N.
5. Go to 2.
Step 3 may pick any maximizer: the algorithm is a nondeterministic relation, not a function.
-/

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- The variables of C1: `SUB` (the subfamily chosen so far), `UNCOV`, and the array `SET`
indexed by `ι` (the index set `{1, …, N}`, `N = |F|`). -/
structure State (ι α : Type) where
  SUB : Finset (Finset α)
  UNCOV : Finset α
  SET : ι → Finset α

/-- Step 1: `SUB = ∅`, `UNCOV = ⋃ S_i`, `SET[i] = S_i`. -/
def init (S : ι → Finset α) : State ι α := ⟨∅, ground S, S⟩

/-- The halting test of Step 2: `UNCOV = ∅`. -/
def Halts (σ : State ι α) : Prop := σ.UNCOV = ∅

/-- One pass through Steps 2–4 with the index `j` chosen at Step 3: C1 does not halt at Step 2,
`|SET[j]|` is maximal among all `|SET[i]|` (any maximizer may be chosen), and Step 4 sets
`SUB = SUB ∪ {S_j}` (the original set `S_j`), `UNCOV = UNCOV − SET[j]`,
`SET[i] = SET[i] − SET[j]` for every `i`. -/
def StepWith (S : ι → Finset α) (σ : State ι α) (j : ι) (σ' : State ι α) : Prop :=
  ¬ Halts σ ∧ (∀ i, (σ.SET i).card ≤ (σ.SET j).card) ∧
    σ' = ⟨insert (S j) σ.SUB, σ.UNCOV \ σ.SET j, fun i => σ.SET i \ σ.SET j⟩

/-- One iteration of C1 for some admissible choice at Step 3. -/
def Step (S : ι → Finset α) (σ σ' : State ι α) : Prop := ∃ j, StepWith S σ j σ'

/-- `F₁` is choosable by C1 given `F`: some admissible pass through the algorithm halts at
Step 2 and returns `SUB = F₁`. -/
def Choosable (S : ι → Finset α) (F₁ : Finset (Finset α)) : Prop :=
  ∃ σ, Relation.ReflTransGen (Step S) (init S) σ ∧ Halts σ ∧ σ.SUB = F₁

end JohnsonApprox.SetCover
