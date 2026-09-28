import Mathlib

namespace JohnsonApprox.Shared

/-- A literal: the variable `x_var` if `pos = true`, its negation `x̄_var` if `pos = false`.
Variables are indexed by natural numbers (the paper indexes them by `i > 0`; any index set of
the same cardinality gives the same problem). -/
structure Literal where
  var : ℕ
  pos : Bool
  deriving DecidableEq

/-- The complementary literal: `x̄` of `x`, and `x` of `x̄` (so `neg (neg l) = l`). -/
def Literal.neg (l : Literal) : Literal := ⟨l.var, !l.pos⟩

/-- A clause is any finite set of literals. -/
abbrev Clause := Finset Literal

/-- A truth assignment is any set `T` of literals containing no complementary pair
`{x_i, x̄_i}`. It may leave variables unassigned. -/
def Assignment := {T : Set Literal // ∀ l ∈ T, l.neg ∉ T}

/-- Truth assignment `T` satisfies clause `C` if `C ∩ T ≠ ∅`. -/
def satisfies (T : Assignment) (C : Clause) : Prop := ∃ l ∈ C, l ∈ T.1

/-- A set of clauses is satisfiable if one truth assignment satisfies every clause in it. -/
def Satisfiable (S' : Finset Clause) : Prop := ∃ T : Assignment, ∀ C ∈ S', satisfies T C

open Classical in
/-- The feasible solutions `SOL_MS(S)`: the subsets `S' ⊆ S` satisfied by one truth assignment. -/
noncomputable def solutions (S : Finset Clause) : Finset (Finset Clause) :=
  S.powerset.filter Satisfiable

/-- The empty subset is always feasible (it is satisfied by the empty assignment). -/
theorem empty_mem_solutions (S : Finset Clause) : ∅ ∈ solutions S := by
  classical
  unfold solutions
  rw [Finset.mem_filter]
  refine ⟨Finset.empty_mem_powerset S, ⟨⟨∅, fun l hl => absurd hl (Set.notMem_empty l)⟩, ?_⟩⟩
  intro C hC
  exact absurd hC (Finset.notMem_empty C)

/-- The optimal measure `S* = MAX{|S'| : S' ∈ SOL_MS(S)}`, a maximum over a finite nonempty set. -/
noncomputable def opt (S : Finset Clause) : ℕ :=
  (solutions S).sup' ⟨∅, empty_mem_solutions S⟩ Finset.card

/-- `S` is an input of `MS(k)`: every clause of `S` contains at least `k` distinct literals. -/
def InMS (k : ℕ) (S : Finset Clause) : Prop := ∀ C ∈ S, k ≤ C.card

end JohnsonApprox.Shared
