import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatGreedy

/-- The state of algorithm B1: the paper's `SUB`, `LEFT`, `TRUE`, and the set `decided` of
variables whose two literals have been removed from `LIT`. Since `L` is infinite, `LIT` is not
stored: a literal `l` is in `LIT` iff `l.var ∉ decided`. -/
structure State where
  SUB : Finset Shared.Clause
  LEFT : Finset Shared.Clause
  TRUE : Finset Shared.Literal
  decided : Finset ℕ

/-- Membership in `LIT = L − ⋃ {y, ȳ}` over the literals `y` chosen so far. -/
def State.inLIT (σ : State) (l : Shared.Literal) : Prop := l.var ∉ σ.decided

/-- Step 1 of B1: `SUB = ∅`, `TRUE = ∅`, `LEFT = S`, `LIT = L` (no variable decided). -/
def init (S : Finset Shared.Clause) : State := ⟨∅, S, ∅, ∅⟩

/-- `YT`: the clauses of `LEFT` containing the literal `y`. -/
def State.YT (σ : State) (y : Shared.Literal) : Finset Shared.Clause := σ.LEFT.filter (fun C => y ∈ C)

/-- The number of clauses of `LEFT` containing the literal `l`. -/
def State.count (σ : State) (l : Shared.Literal) : ℕ := (σ.YT l).card

/-- The halting test of Step 2: no literal in `LIT` is contained in any clause of `LEFT`. -/
def Halts (σ : State) : Prop := ∀ C ∈ σ.LEFT, ∀ l ∈ C, ¬ σ.inLIT l

/-- One pass through Steps 2–4 of B1 with chosen literal `y`: Step 2 does not halt; Step 3 lets
`y` be a literal in `LIT` contained in the most clauses of `LEFT` (any maximizer, of either sign);
Step 4 sets `SUB = SUB ∪ YT`, `LEFT = LEFT − YT`, `TRUE = TRUE ∪ {y}`, `LIT = LIT − {y, ȳ}`. -/
def StepWith (σ : State) (y : Shared.Literal) (σ' : State) : Prop :=
  ¬ Halts σ ∧ σ.inLIT y ∧ (∀ z : Shared.Literal, σ.inLIT z → σ.count z ≤ σ.count y) ∧
    σ' = ⟨σ.SUB ∪ σ.YT y, σ.LEFT \ σ.YT y, insert y σ.TRUE, insert y.var σ.decided⟩

/-- One iteration of B1, for some admissible choice of `y`. -/
def Step (σ σ' : State) : Prop := ∃ y, StepWith σ y σ'

/-- `σ` is a state B1 can be in after finitely many iterations on input `S`. -/
def Reachable (S : Finset Shared.Clause) (σ : State) : Prop := Relation.ReflTransGen Step (init S) σ

/-- `X` is choosable by B1 on input `S`: some admissible run halts with `SUB = X`. -/
def Choosable (S : Finset Shared.Clause) (X : Finset Shared.Clause) : Prop :=
  ∃ σ, Reachable S σ ∧ Halts σ ∧ σ.SUB = X

end JohnsonApprox.MaxSatGreedy
