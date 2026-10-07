import Mathlib

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 264, §3: `|x|`, the maximum of the absolute values of the coordinates of
`x` (the value is `0` on the zero-dimensional space). -/
noncomputable def maxNorm {k : ℕ} (x : Fin k → ℝ) : ℝ := ⨆ i, |x i|

/-- Hoffman 1952, p. 264, §3: `‖x‖`, the sum of the absolute values of the coordinates of `x`. -/
def sumNorm {k : ℕ} (x : Fin k → ℝ) : ℝ := ∑ i, |x i|

/-- The Gram matrix `g_ij = A_i · A_j` of the rows of `A` (pp. 265). -/
def gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => A i ⬝ᵥ A j

/-- (6), p. 264: `a_S`, the largest absolute value of the coordinates of the rows `A_i`,
`i ∈ S`. -/
noncomputable def aS {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) : ℝ :=
  ⨆ i : S, ⨆ j, |A i j|

/-- The probability simplex on the index set `S`: weights `λ_j ≥ 0`, zero off `S`, with
`∑_{j ∈ S} λ_j = 1`. -/
def simplexOn {m : ℕ} (S : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {l | (∀ j, 0 ≤ l j) ∧ (∀ j, j ∉ S → l j = 0) ∧ ∑ j ∈ S, l j = 1}

/-- (7), p. 265: `v_S = min_λ max_{i ∈ S} ∑_{j ∈ S} g_ij λ_j`, the minimum over the simplex on
`S` (the value of the zero-sum game with matrix `g_ij`, `i, j ∈ S`). Used for nonempty `S`. -/
noncomputable def vS {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) : ℝ :=
  ⨅ l : simplexOn S, ⨆ i : S, ∑ j ∈ S, gram A i j * (l : Fin m → ℝ) j

/-- (8), p. 265: `c = max_{v_S > 0} a_S / v_S`, the maximum over the nonempty subsets `S` of the
rows with `v_S > 0` (`0` if there is none, which happens only when every row is `0`). -/
noncomputable def constC8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ S : {S : Finset (Fin m) // S.Nonempty ∧ 0 < vS A S}, aS A S.1 / vS A S.1

/-- (9), p. 265: `v = min_{i,j} A_i · A_j`. -/
noncomputable def vMin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ⨅ i, ⨅ j, gram A i j

/-- (9), p. 265: `a = max_{i,j} |a_ij|`. -/
noncomputable def aMax {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ⨆ i, ⨆ j, |A i j|

/-- (10), p. 265: `w = min_i (g_ii + ∑_{j, g_ij < 0} g_ij)`, with `g` the Gram matrix of all the
rows of `A` and `j` ranging over the rows. -/
noncomputable def wConst {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨅ i, (gram A i i + ∑ j ∈ Finset.univ.filter (fun j => gram A i j < 0), gram A i j)

end HoffmanBound.ErrorBound
