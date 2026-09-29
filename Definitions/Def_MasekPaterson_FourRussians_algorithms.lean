import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

variable {α : Type*}

/-- Algorithm Y's two step matrices, computed together: `algYCell γ m C D R S i j` is the pair
`(T(i, j), U(i, j))` for `1 ≤ i, j ≤ m`, with the boundary cells `T(i, 0) := R(i)` and
`U(0, j) := S(j)` (`1 ≤ i, j ≤ m`) and, for `1 ≤ i, j ≤ m`,
`T(i,j) := min{R_{C_i,D_j} − U(i−1,j), D_{C_i}, I_{D_j} + T(i,j−1) − U(i−1,j)}` and
`U(i,j) := min{R_{C_i,D_j} − T(i,j−1), D_{C_i} + U(i−1,j) − T(i,j−1), I_{D_j}}`.
Strings and step vectors are 1-based in the paper: `C_i` is `C ⟨i-1, _⟩`, `R(i)` is
`R ⟨i-1, _⟩`. Cells the algorithm never assigns (outside the ranges above, and the unused
component of a boundary cell) are `0`. -/
noncomputable def algYCell (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ) :
    ℕ → ℕ → ℝ × ℝ
  | 0, 0 => (0, 0)
  | i + 1, 0 => (if h : i < m then R ⟨i, h⟩ else 0, 0)
  | 0, j + 1 => (0, if h : j < m then S ⟨j, h⟩ else 0)
  | i + 1, j + 1 =>
    if h : i < m ∧ j < m then
      -- `Tl` is `T(i+1, j)` and `Uu` is `U(i, j+1)` in the paper's 1-based coordinates
      let Tl := (algYCell γ m C D R S (i + 1) j).1
      let Uu := (algYCell γ m C D R S i (j + 1)).2
      let r := replCost γ (C ⟨i, h.1⟩) (D ⟨j, h.2⟩)
      let d := delCost γ (C ⟨i, h.1⟩)
      let n := insCost γ (D ⟨j, h.2⟩)
      (min (min (r - Uu) d) (n + Tl - Uu), min (min (r - Tl) (d + Uu - Tl)) n)
    else (0, 0)

/-- Algorithm Y's matrix `T` of vertical steps. -/
noncomputable def algY_T (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ)
    (i j : ℕ) : ℝ :=
  (algYCell γ m C D R S i j).1

/-- Algorithm Y's matrix `U` of horizontal steps. -/
noncomputable def algY_U (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ)
    (i j : ℕ) : ℝ :=
  (algYCell γ m C D R S i j).2

/-- Algorithm Y on one submatrix (the value it stores, and `Fetch` returns): for strings
`C, D` of length `m` and initial step vectors `R` (left column, vertical steps) and `S`
(top row, horizontal steps), the final step vectors `R' = ⟨T(1,m), …, T(m,m)⟩` (right column)
and `S' = ⟨U(m,1), …, U(m,m)⟩` (bottom row). -/
noncomputable def blockY (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ) :
    (Fin m → ℝ) × (Fin m → ℝ) :=
  (fun k => algY_T γ m C D R S (k.val + 1) m, fun k => algY_U γ m C D R S m (k.val + 1))

/-- The `(b+1)`-th length-`m` block `A^{bm+1, bm+m}` of `A` as a vector `Fin m → α`
(its `k`-th entry, 0-based, is `A_{bm+k+1}`), when it fits: `(b+1) m ≤ |A|`. -/
def blockStr (A : List α) (m b : ℕ) (h : (b + 1) * m ≤ A.length) : Fin m → α :=
  fun k => A[b * m + k.val]'(by
    have hk := k.isLt
    have : (b + 1) * m = b * m + m := Nat.succ_mul b m
    omega)

/-- Algorithm Z's matrices, computed together: `algZCell γ m A B i j = (P(i, j), Q(i, j))`.
With `a = |A|/m` and `b = |B|/m`:
`P(i, 0) := ⟨D_{A_{(i−1)m+1}}, …, D_{A_{im}}⟩` for `1 ≤ i ≤ a`,
`Q(0, j) := ⟨I_{B_{(j−1)m+1}}, …, I_{B_{jm}}⟩` for `1 ≤ j ≤ b`, and for `1 ≤ i ≤ a`,
`1 ≤ j ≤ b`, `⟨P(i,j), Q(i,j)⟩ := Fetch(P(i,j−1), Q(i−1,j), A^{(i−1)m+1,im}, B^{(j−1)m+1,jm})`
where `Fetch(R, S, C, D)` is Algorithm Y's result `blockY γ m C D R S`. Cells the algorithm
never assigns are the zero vector. -/
noncomputable def algZCell (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) :
    ℕ → ℕ → (Fin m → ℝ) × (Fin m → ℝ)
  | 0, 0 => (0, 0)
  | i + 1, 0 =>
    (if h : (i + 1) * m ≤ A.length then fun k => delCost γ (blockStr A m i h k) else 0, 0)
  | 0, j + 1 =>
    (0, if h : (j + 1) * m ≤ B.length then fun k => insCost γ (blockStr B m j h k) else 0)
  | i + 1, j + 1 =>
    if h : (i + 1) * m ≤ A.length ∧ (j + 1) * m ≤ B.length then
      blockY γ m (blockStr A m i h.1) (blockStr B m j h.2)
        (algZCell γ m A B (i + 1) j).1 (algZCell γ m A B i (j + 1)).2
    else (0, 0)

/-- Algorithm Z's matrix `P` of column step vectors. -/
noncomputable def algZ_P (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) (i j : ℕ) : Fin m → ℝ :=
  (algZCell γ m A B i j).1

/-- Algorithm Z's matrix `Q` of row step vectors. -/
noncomputable def algZ_Q (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) (i j : ℕ) : Fin m → ℝ :=
  (algZCell γ m A B i j).2

/-- The value `cost` returned by Algorithm Z:
`∑_{i=1}^{|A|/m} Sum(P(i, 0)) + ∑_{j=1}^{|B|/m} Sum(Q(|A|/m, j))`. -/
noncomputable def algZ (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) : ℝ :=
  (∑ i ∈ Finset.Icc 1 (A.length / m), ∑ k, algZ_P γ m A B i 0 k) +
    ∑ j ∈ Finset.Icc 1 (B.length / m), ∑ k, algZ_Q γ m A B (A.length / m) j k

end MasekPaterson.FourRussians
