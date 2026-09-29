import Mathlib

namespace MasekPaterson.Shared

/-- An edit operation `a → b` (Masek–Paterson §1.1): a pair `(a, b)` of strings of length
at most one (encoded as `Option α`), other than the pair `(λ, λ)` of two null strings. -/
structure EditOp (α : Type*) where
  /-- the string `a` that is replaced (`none` is the null string `λ`) -/
  src : Option α
  /-- the string `b` it is replaced by (`none` is the null string `λ`) -/
  tgt : Option α
  /-- `(a, b) ≠ (λ, λ)` -/
  not_null : ¬ (src = none ∧ tgt = none)

variable {α : Type*}

/-- `A → B via a → b`: `A = σ a τ` and `B = σ b τ` for some strings `σ, τ`. -/
def Yields (o : EditOp α) (A B : List α) : Prop :=
  ∃ σ τ : List α, A = σ ++ o.src.toList ++ τ ∧ B = σ ++ o.tgt.toList ++ τ

/-- `S` takes `A` to `B`: there is an `S`-derivation `A = C₀ → C₁ → ⋯ → C_m = B`
with `C_{i-1} → C_i` via `s_i`, where `S = s₁, …, s_m`. -/
inductive Takes : List (EditOp α) → List α → List α → Prop
  | nil (A : List α) : Takes [] A A
  | cons {s : EditOp α} {S : List (EditOp α)} {A C B : List α} :
      Yields s A C → Takes S C B → Takes (s :: S) A B

/-- The cost `γ(S) = ∑_{1 ≤ i ≤ m} γ(s_i)` of an edit sequence. -/
def seqCost (γ : EditOp α → ℝ) (S : List (EditOp α)) : ℝ :=
  (S.map γ).sum

/-- The edit distance `δ(γ, A, B) = min {γ(S) | S is an edit sequence taking A to B}`,
defined as the infimum of that set of real numbers. -/
noncomputable def editDist (γ : EditOp α → ℝ) (A B : List α) : ℝ :=
  sInf {c : ℝ | ∃ S : List (EditOp α), Takes S A B ∧ c = seqCost γ S}

/-- The replacement operation `a → b` (with `a = b` allowed). -/
def replOp (a b : α) : EditOp α := ⟨some a, some b, by simp⟩

/-- The deletion operation `a → λ`. -/
def delOp (a : α) : EditOp α := ⟨some a, none, by simp⟩

/-- The insertion operation `λ → a`. -/
def insOp (a : α) : EditOp α := ⟨none, some a, by simp⟩

/-- `R_{a,b} = γ(a → b)`, the cost of replacing `a` with `b`. -/
def replCost (γ : EditOp α → ℝ) (a b : α) : ℝ := γ (replOp a b)

/-- `D_a = γ(a → λ)`, the cost of deleting `a`. -/
def delCost (γ : EditOp α → ℝ) (a : α) : ℝ := γ (delOp a)

/-- `I_a = γ(λ → a)`, the cost of inserting `a`. -/
def insCost (γ : EditOp α → ℝ) (a : α) : ℝ := γ (insOp a)

/-- The edit matrix entry `δ_{i,j} = δ(γ, A^i, B^j)`, where `A^i = A₁ ⋯ A_i` is the prefix
of length `i` (`A^0 = λ`). -/
noncomputable def dmat (γ : EditOp α → ℝ) (A B : List α) (i j : ℕ) : ℝ :=
  editDist γ (A.take i) (B.take j)

/-- The normalization of §1.1: `γ(a → b) = δ(γ, a, b)` for every edit operation `a → b`. -/
def IsNormalized (γ : EditOp α → ℝ) : Prop :=
  ∀ o : EditOp α, γ o = editDist γ o.src.toList o.tgt.toList

end MasekPaterson.Shared
