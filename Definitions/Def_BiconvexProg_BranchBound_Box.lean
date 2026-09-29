import Mathlib

namespace BiconvexProg.BranchBound

/-- A box `{(x, y) : l ≤ x ≤ L, m ≤ y ≤ M}` in `ℝⁿ × ℝⁿ`, given by its four bound vectors
(Al-Khayyal–Falk 1983, pp. 274, 276). Degenerate boxes (`l i = L i` or `m i = M i`) are allowed. -/
structure Box (n : ℕ) where
  /-- lower bounds on `x` -/
  l : Fin n → ℝ
  /-- upper bounds on `x` -/
  L : Fin n → ℝ
  /-- lower bounds on `y` -/
  m : Fin n → ℝ
  /-- upper bounds on `y` -/
  M : Fin n → ℝ

namespace Box

variable {n : ℕ}

/-- The point set `{(x, y) : l ≤ x ≤ L, m ≤ y ≤ M}` of a box (coordinatewise order). -/
def toSet (B : Box n) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  Set.Icc B.l B.L ×ˢ Set.Icc B.m B.M

/-- The `i`-th coordinate rectangle `Ω_i = {(x_i, y_i) : l_i ≤ x_i ≤ L_i, m_i ≤ y_i ≤ M_i}`. -/
def rect (B : Box n) (i : Fin n) : Set (ℝ × ℝ) :=
  Set.Icc (B.l i) (B.L i) ×ˢ Set.Icc (B.m i) (B.M i)

/-- `B'` is a sub-box of `B`: `l ≤ l'`, `L' ≤ L`, `m ≤ m'`, `M' ≤ M` coordinatewise. -/
def IsSubBox (B' B : Box n) : Prop :=
  B.l ≤ B'.l ∧ B'.L ≤ B.L ∧ B.m ≤ B'.m ∧ B'.M ≤ B.M

/-- The four children of `B` obtained by splitting its `I`-th rectangle at the point `(a, b)`
(p. 278, Figure 1), numbered counterclockwise from the lower-left subrectangle
(`0, 1, 2, 3` stand for the paper's `21, 22, 23, 24`):
* child 0: `(l_I, L_I, m_I, M_I) := (l_I, a, m_I, b)`;
* child 1: `(a, L_I, m_I, b)`;
* child 2: `(a, L_I, b, M_I)`;
* child 3: `(l_I, a, b, M_I)`;
and all rectangles `i ≠ I` are kept. -/
def child (B : Box n) (I : Fin n) (a b : ℝ) : Fin 4 → Box n :=
  ![⟨B.l, Function.update B.L I a, B.m, Function.update B.M I b⟩,
    ⟨Function.update B.l I a, B.L, B.m, Function.update B.M I b⟩,
    ⟨Function.update B.l I a, B.L, Function.update B.m I b, B.M⟩,
    ⟨B.l, Function.update B.L I a, Function.update B.m I b, B.M⟩]

/-- The multiset of the four children of `B` split at index `I` and point `(a, b)`. -/
def split (B : Box n) (I : Fin n) (a b : ℝ) : Multiset (Box n) :=
  {B.child I a b 0, B.child I a b 1, B.child I a b 2, B.child I a b 3}

end Box

end BiconvexProg.BranchBound
