import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace JohnsonApprox.MaxSatWeighted

/-- The state of algorithm B2: the paper's `SUB`, `LEFT`, `TRUE`, the set `decided` of variables
whose two literals have been removed from `LIT`, and the current clause weights `w`. Since `L` is
infinite, `LIT` is not stored: a literal `l` is in `LIT` iff `l.var ∉ decided`. -/
structure State where
  SUB : Finset Shared.Clause
  LEFT : Finset Shared.Clause
  TRUE : Finset Shared.Literal
  decided : Finset ℕ
  w : Shared.Clause → ℚ

/-- Membership in `LIT = L − ⋃ {y, ȳ}` over the literals `y` considered so far. -/
def State.inLIT (σ : State) (l : Shared.Literal) : Prop := l.var ∉ σ.decided

/-- Step 1 of B2: every clause `C` gets weight `w(C) = 2^{-|C|}`; `SUB = TRUE = ∅`, `LIT = L`
(no variable decided), `LEFT = S`. -/
def init (S : Finset Shared.Clause) : State := ⟨∅, S, ∅, ∅, fun C => 1 / 2 ^ C.card⟩

/-- `YT`: the clauses of `LEFT` containing the literal `y`. -/
def State.YT (σ : State) (y : Shared.Literal) : Finset Shared.Clause := σ.LEFT.filter (fun C => y ∈ C)

/-- `YF`: the clauses of `LEFT` containing the complementary literal `ȳ`. -/
def State.YF (σ : State) (y : Shared.Literal) : Finset Shared.Clause := σ.LEFT.filter (fun C => y.neg ∈ C)

/-- The total current weight `Σ_{C ∈ A} w(C)` of a set `A` of clauses. -/
def State.weight (σ : State) (A : Finset Shared.Clause) : ℚ := ∑ C ∈ A, σ.w C

/-- The weight function after setting `w(C) = 2w(C)` for each `C ∈ A`. -/
def doubleOn (w : Shared.Clause → ℚ) (A : Finset Shared.Clause) : Shared.Clause → ℚ :=
  fun C => if C ∈ A then 2 * w C else w C

/-- The halting test of Step 2: no literal in any clause of `LEFT` is in `LIT`. -/
def Halts (σ : State) : Prop := ∀ C ∈ σ.LEFT, ∀ l ∈ C, ¬ σ.inLIT l

/-- The state after Steps 4–5 of B2 with chosen literal `y`, computed from the weights before the
update. If `Σ_{C∈YT} w(C) ≥ Σ_{C∈YF} w(C)`: `TRUE = TRUE ∪ {y}`, `SUB = SUB ∪ YT`,
`LEFT = LEFT − YT`, and `w(C) = 2w(C)` for each `C ∈ YF`. Otherwise: `TRUE = TRUE ∪ {ȳ}`,
`SUB = SUB ∪ YF`, `LEFT = LEFT − YF`, and `w(C) = 2w(C)` for each `C ∈ YT`. In both cases
`LIT = LIT − {y, ȳ}`. -/
def State.update (σ : State) (y : Shared.Literal) : State :=
  if σ.weight (σ.YF y) ≤ σ.weight (σ.YT y) then
    ⟨σ.SUB ∪ σ.YT y, σ.LEFT \ σ.YT y, insert y σ.TRUE, insert y.var σ.decided,
      doubleOn σ.w (σ.YF y)⟩
  else
    ⟨σ.SUB ∪ σ.YF y, σ.LEFT \ σ.YF y, insert y.neg σ.TRUE, insert y.var σ.decided,
      doubleOn σ.w (σ.YT y)⟩

/-- One pass through Steps 2–5 of B2 with chosen literal `y`: Step 2 does not halt; Step 3 lets
`y` be any literal (of either sign) occurring both in `LIT` and in a clause of `LEFT`; Steps 4–5
produce `σ'`. -/
def StepWith (σ : State) (y : Shared.Literal) (σ' : State) : Prop :=
  ¬ Halts σ ∧ σ.inLIT y ∧ (∃ C ∈ σ.LEFT, y ∈ C) ∧ σ' = σ.update y

/-- One iteration of B2, for some admissible choice of `y`. -/
def Step (σ σ' : State) : Prop := ∃ y, StepWith σ y σ'

/-- `σ` is a state B2 can be in after finitely many iterations on input `S`. -/
def Reachable (S : Finset Shared.Clause) (σ : State) : Prop := Relation.ReflTransGen Step (init S) σ

/-- `X` is choosable by B2 on input `S`: some admissible run halts and returns `SUB = X`. -/
def Choosable (S : Finset Shared.Clause) (X : Finset Shared.Clause) : Prop :=
  ∃ σ, Reachable S σ ∧ Halts σ ∧ σ.SUB = X

end JohnsonApprox.MaxSatWeighted
