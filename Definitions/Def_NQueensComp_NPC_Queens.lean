import Mathlib

namespace NQueensComp.NPC

/-- A queen `q = (α, β)` with `0 ≤ α, 0 ≤ β` (Definition 1): `α` is its column, `β` its row. -/
abbrev Queen := ℕ × ℕ

/-- The column `col(q) = α` of `q = (α, β)`. -/
def col (q : Queen) : ℕ := q.1

/-- The row `row(q) = β` of `q = (α, β)`. -/
def row (q : Queen) : ℕ := q.2

/-- The sum-diagonal `α + β` of `q = (α, β)`. -/
def sumDiag (q : Queen) : ℕ := q.1 + q.2

/-- The difference-diagonal `α − β` of `q = (α, β)`, an integer (no truncated subtraction). -/
def diffDiag (q : Queen) : ℤ := (q.1 : ℤ) - (q.2 : ℤ)

/-- The size `‖q‖ = max(α, β)`. -/
def size (q : Queen) : ℕ := max q.1 q.2

/-- `q` fits on board size `n`: `‖q‖ < n`. -/
def FitsOn (n : ℕ) (q : Queen) : Prop := size q < n

/-- `q` attacks `q₁`: `q ≠ q₁` and they share a column, a row, a sum-diagonal or a
difference-diagonal (Definition 1). -/
def Attacks (q q₁ : Queen) : Prop :=
  q ≠ q₁ ∧ (col q = col q₁ ∨ row q = row q₁ ∨ sumDiag q = sumDiag q₁ ∨ diffDiag q = diffDiag q₁)

/-- No queen of `Q` attacks another queen of `Q`. -/
def NonAttacking (Q : Finset Queen) : Prop :=
  ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, ¬ Attacks q₁ q₂

/-- `Q + q₁ = {q + q₁ | q ∈ Q}` (Definition 1); `+` on `ℕ × ℕ` is componentwise. -/
def shiftSet (Q : Finset Queen) (q₁ : Queen) : Finset Queen :=
  Q.image (fun q => q + q₁)

/-- `iQ = {iq | q ∈ Q}` with `iq = (iα, iβ)` (Definition 1). -/
def scaleSet (i : ℕ) (Q : Finset Queen) : Finset Queen :=
  Q.image (fun q => i • q)

/-- `Q + Q₁ = {q + q₁ | q ∈ Q, q₁ ∈ Q₁}` (Definition 1). -/
def sumSet (Q Q₁ : Finset Queen) : Finset Queen :=
  (Q ×ˢ Q₁).image (fun p => p.1 + p.2)

/-- `Q` is a solution to the `n`-Queens problem (Problem 1): `n ≥ 1`, every queen of `Q` fits on
board size `n`, `|Q| = n`, and no two distinct queens of `Q` attack each other. -/
def IsNQueensSol (n : ℕ) (Q : Finset Queen) : Prop :=
  1 ≤ n ∧ (∀ q ∈ Q, FitsOn n q) ∧ Q.card = n ∧ NonAttacking Q

/-- `Q` is a modular solution to the `n`-Queens problem (Problem 1): a solution such that any two
distinct queens have sum-diagonals and difference-diagonals that differ modulo `n`. -/
def IsModularSol (n : ℕ) (Q : Finset Queen) : Prop :=
  IsNQueensSol n Q ∧
    ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, q₁ ≠ q₂ →
      ¬ ((sumDiag q₁ : ℤ) ≡ (sumDiag q₂ : ℤ) [ZMOD (n : ℤ)]) ∧
        ¬ (diffDiag q₁ ≡ diffDiag q₂ [ZMOD (n : ℤ)])

/-- The 19-queens solution `Q₁₉` of Definition 5 (p. 822). -/
def Q19 : Finset Queen :=
  {(0, 8), (1, 12), (2, 17), (3, 7), (4, 10), (5, 15), (6, 1), (7, 16), (8, 13), (9, 2),
   (10, 6), (11, 18), (12, 3), (13, 5), (14, 11), (15, 9), (16, 14), (17, 0), (18, 4)}

/-- `Aₙ = {(i, 2i mod n) | 0 ≤ i < n}` (Definition 5). -/
def A (n : ℕ) : Finset Queen :=
  (Finset.range n).image (fun i => (i, 2 * i % n))

/-- `Bₙ = {(2i mod n, i) | 0 ≤ i < n}` (Definition 5). -/
def B (n : ℕ) : Finset Queen :=
  (Finset.range n).image (fun i => (2 * i % n, i))

end NQueensComp.NPC
