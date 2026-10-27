import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- No two distinct queens of `P` share a column or a row. -/
def DistinctRowsCols (P : Finset Queen) : Prop :=
  ∀ q₁ ∈ P, ∀ q₂ ∈ P, q₁ ≠ q₂ → col q₁ ≠ col q₂ ∧ row q₁ ≠ row q₂

/-- An instance `M₂ = ⟨n, P⟩` of n-Queens Completion (Problem 2). -/
structure Inst2 where
  /-- board size -/
  n : ℕ
  /-- the queens already placed -/
  P : Finset Queen

/-- `⟨n, P⟩` is an instance of Problem 2: every queen of `P` fits on board size `n` and no two
queens of `P` share a column or a row.  The board size is `n ≥ 1` (Problem 1); `P` may attack
along a diagonal. -/
def Inst2.Valid (M : Inst2) : Prop :=
  1 ≤ M.n ∧ (∀ q ∈ M.P, FitsOn M.n q) ∧ DistinctRowsCols M.P

/-- `S₂` is a solution to `⟨n, P⟩` (Problem 2): a solution to the `n`-Queens problem with
`P ⊆ S₂`. -/
def Inst2.IsSol (M : Inst2) (S : Finset Queen) : Prop :=
  IsNQueensSol M.n S ∧ M.P ⊆ S

/-- An instance `M₃ = ⟨n, P, C, R⟩` of Problem 3. -/
structure Inst3 where
  /-- board size -/
  n : ℕ
  /-- the queens already placed -/
  P : Finset Queen
  /-- the columns that must be used -/
  C : Finset ℕ
  /-- the rows that must be used -/
  R : Finset ℕ

/-- `⟨n, P, C, R⟩` is an instance of Problem 3: `⟨n, P⟩` is an instance of Problem 2,
`|R| = |C|`, no queen of `P` has its column in `C` or its row in `R`, and (the reading used by the
proofs of Lemmas 11 and 22) `C, R ⊆ {0, …, n − 1}`. -/
def Inst3.Valid (M : Inst3) : Prop :=
  (Inst2.mk M.n M.P).Valid ∧ M.C.card = M.R.card ∧
    (∀ q ∈ M.P, col q ∉ M.C ∧ row q ∉ M.R) ∧
    (∀ c ∈ M.C, c < M.n) ∧ (∀ r ∈ M.R, r < M.n)

/-- `S₃` is a solution to `⟨n, P, C, R⟩` (Problem 3): `|S₃| = |C| + |P|`, `P ⊆ S₃`, no two queens
of `S₃` attack each other, and every `(α, β) ∈ S₃ \ P` has `α ∈ C` and `β ∈ R`. -/
def Inst3.IsSol (M : Inst3) (S : Finset Queen) : Prop :=
  S.card = M.C.card + M.P.card ∧ M.P ⊆ S ∧ NonAttacking S ∧
    ∀ q ∈ S \ M.P, col q ∈ M.C ∧ row q ∈ M.R

/-- An instance `M₄ = ⟨n, C, R, D⁻, D⁺⟩` of the Excluded Diagonals problem (Problem 4). -/
structure Inst4 where
  /-- board size -/
  n : ℕ
  /-- the columns that must be used -/
  C : Finset ℕ
  /-- the rows that must be used -/
  R : Finset ℕ
  /-- the excluded difference-diagonals `D⁻` -/
  Dm : Finset ℤ
  /-- the excluded sum-diagonals `D⁺` -/
  Dp : Finset ℕ

/-- The instance `⟨n, {}, C, R⟩` of Problem 3 underlying `⟨n, C, R, D⁻, D⁺⟩`. -/
def Inst4.toInst3 (M : Inst4) : Inst3 := ⟨M.n, ∅, M.C, M.R⟩

/-- `⟨n, C, R, D⁻, D⁺⟩` is an instance of Problem 4: `⟨n, {}, C, R⟩` is an instance of Problem 3,
`D⁻ ⊆ {−(n−1), …, n−1}` and `D⁺ ⊆ {0, …, 2n−2}`. -/
def Inst4.Valid (M : Inst4) : Prop :=
  M.toInst3.Valid ∧
    (∀ d ∈ M.Dm, -((M.n : ℤ) - 1) ≤ d ∧ d ≤ (M.n : ℤ) - 1) ∧
    (∀ d ∈ M.Dp, (d : ℤ) ≤ 2 * (M.n : ℤ) - 2)

/-- `S₄` is a solution to `⟨n, C, R, D⁻, D⁺⟩` (Problem 4): a solution to `⟨n, {}, C, R⟩` such that
every queen `(α, β) ∈ S₄` has `α − β ∉ D⁻` and `α + β ∉ D⁺`. -/
def Inst4.IsSol (M : Inst4) (S : Finset Queen) : Prop :=
  M.toInst3.IsSol S ∧ ∀ q ∈ S, diffDiag q ∉ M.Dm ∧ sumDiag q ∉ M.Dp

/-- An instance `M₅ = {M₄,ₐ | 0 ≤ a < |M₅|}` of Problem 5, as the indexed family
`[M₄,₀, …, M₄,ₖ₋₁]`. -/
abbrev Inst5 := List Inst4

/-- `M₅` is an instance of Problem 5: each `M₄,ₐ` is an instance of Problem 4 with `D⁺ = {}`. -/
def Inst5Valid (Ms : Inst5) : Prop :=
  ∀ M ∈ Ms, M.Valid ∧ M.Dp = ∅

/-- `[S₄,₀, …, S₄,ₖ₋₁]` is a solution to `[M₄,₀, …, M₄,ₖ₋₁]` (Problem 5): each `S₄,ₐ` is a solution
to `M₄,ₐ`, and for indices `a ≠ b` no queen of `S₄,ₐ` has the same sum-diagonal as a queen of
`S₄,b`. -/
def Inst5IsSol (Ms : Inst5) (Ss : List (Finset Queen)) : Prop :=
  List.Forall₂ (fun (M : Inst4) (S : Finset Queen) => M.IsSol S) Ms Ss ∧
    ∀ a < Ss.length, ∀ b < Ss.length, a ≠ b →
      ∀ qa ∈ Ss.getD a ∅, ∀ qb ∈ Ss.getD b ∅, sumDiag qa ≠ sumDiag qb

/-- An instance `M₆ = ⟨V, C⟩` of Restricted 1-in-3-SAT (Problem 6), as the list of its clauses
`[c₀, c₁, …]` in the fixed clause order; variables are natural numbers. -/
abbrev Inst6 := List (Finset ℕ)

/-- `V = {v | ∃ c ∈ C, v ∈ c}`, the variables occurring in some clause. -/
def vars (cs : Inst6) : Finset ℕ := cs.foldr (fun c V => c ∪ V) ∅

/-- The number of clauses of `cs` that contain the variable `v`. -/
def occurrences (cs : Inst6) (v : ℕ) : ℕ := cs.countP (fun c => decide (v ∈ c))

/-- `cs` is an instance of Problem 6: its clauses are distinct (`C` is a set), every clause is a
set of exactly three variables, and every variable occurs in at most three clauses. -/
def Inst6Valid (cs : Inst6) : Prop :=
  cs.Nodup ∧ (∀ c ∈ cs, c.card = 3) ∧ ∀ v : ℕ, occurrences cs v ≤ 3

/-- A solution of Problem 6, given by the set `T ⊆ V` of variables assigned `true`: every clause
contains exactly one variable of `T`.  (Truth assignments `S₆ : V → {true, false}` correspond
bijectively to subsets `T ⊆ V`.) -/
def Inst6IsSol (cs : Inst6) (T : Finset ℕ) : Prop :=
  T ⊆ vars cs ∧ ∀ c ∈ cs, (c ∩ T).card = 1

end NQueensComp.NPC
