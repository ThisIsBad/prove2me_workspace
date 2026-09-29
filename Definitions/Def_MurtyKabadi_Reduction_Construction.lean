import Mathlib

namespace MurtyKabadi.Reduction

/-- `f₁(y, s)` (p. 123). -/
noncomputable def f1 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (y s : Fin n → ℝ) : ℝ :=
  (∑ j, (d j : ℝ) * y j - d0) ^ 2 + (δ : ℝ) * (∑ j, (y j + s j - 1) ^ 2) + ∑ j, y j * s j

/-- `f₂(y, s) = f₁(y, s) + 2 d₀ ∑ d_j y_j (1 − y_j)` (p. 123). -/
noncomputable def f2 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (y s : Fin n → ℝ) : ℝ :=
  f1 d d0 δ y s + 2 * (d0 : ℝ) * ∑ j, (d j : ℝ) * y j * (1 - y j)

/-- `f₄(y, s)` (p. 124). -/
noncomputable def f4 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (y s : Fin n → ℝ) : ℝ :=
  (∑ j, (d j : ℝ) * y j) ^ 2 + (δ : ℝ) * ∑ j, (y j + s j) ^ 2 + ∑ j, y j * s j
    - 2 * (d0 : ℝ) * ∑ j, (d j : ℝ) * y j ^ 2
    + (((d0 : ℝ) ^ 2 - n * δ) / (n : ℝ) ^ 2) * (∑ j, (y j + s j)) ^ 2

/-- `f₅(y, s) = f₄(y, s) − (ε / n²) (∑ (y_j + s_j))²` (p. 124). -/
noncomputable def f5 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) (y s : Fin n → ℝ) : ℝ :=
  f4 d d0 δ y s - ((ε : ℝ) / (n : ℝ) ^ 2) * (∑ j, (y j + s j)) ^ 2

/-- The polytope `P = {(y, s) : y ≥ 0, s ≥ 0, ∑ (y_j + s_j) = n}` (p. 124). -/
def P (n : ℕ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ ∑ j, (p.1 j + p.2 j) = n}

/-- The symmetric matrix of the quadratic form `f₅` on the variables `(y, s)`, indexed by
`Fin n ⊕ Fin n` (`Sum.inl j ↔ y_j`, `Sum.inr j ↔ s_j`). With `c = (d₀² − nδ − ε)/n²`:
`(y_i, y_j)` entry `d_i d_j + c` (plus `δ − 2 d₀ d_j` if `i = j`); `(y_i, s_j)` and `(s_j, y_i)`
entries `c` (plus `δ + 1/2` if `i = j`); `(s_i, s_j)` entry `c` (plus `δ` if `i = j`). -/
noncomputable def mkMatrix {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  let c : ℝ := ((d0 : ℝ) ^ 2 - n * δ - ε) / (n : ℝ) ^ 2
  fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl j =>
        (d i : ℝ) * d j + c + if i = j then (δ : ℝ) - 2 * d0 * d j else 0
    | Sum.inl i, Sum.inr j => c + if i = j then (δ : ℝ) + 1 / 2 else 0
    | Sum.inr i, Sum.inl j => c + if i = j then (δ : ℝ) + 1 / 2 else 0
    | Sum.inr i, Sum.inr j => c + if i = j then (δ : ℝ) else 0

end MurtyKabadi.Reduction
