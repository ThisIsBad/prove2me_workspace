import Mathlib

open Matrix

namespace GPSAnalysis.Core

/-- The direction matrix `D = G Z̄` (p. 892): column `j` is `d_j = G z̄_j`, with `G ∈ ℝ^{n×n}`
and `Z̄` an integer `n × |D|` matrix. -/
def dirMatrix {n p : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (Zbar : Matrix (Fin n) (Fin p) ℤ) :
    Matrix (Fin n) (Fin p) ℝ :=
  G * Zbar.map (fun z : ℤ => (z : ℝ))

/-- Column `j` of a direction matrix, as a vector of `ℝⁿ`. -/
def direction {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : Fin n → ℝ :=
  fun i => D i j

/-- The set of nonnegative linear combinations of the columns of `D` indexed by `S`. -/
def nonnegSpan {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    Set (Fin n → ℝ) :=
  {v | ∃ c : Fin p → ℝ, (∀ j, 0 ≤ c j) ∧ v = ∑ j ∈ S, c j • direction D j}

/-- The columns of `D` indexed by `S` form a positive spanning set of `ℝⁿ` (p. 892): their
nonnegative linear combinations span `ℝⁿ`. -/
def IsPositiveSpanning {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) : Prop :=
  nonnegSpan D S = Set.univ

/-- The mesh (2.4): `M_k = {x_k + Δ_k D z : z ∈ ℤ₊^{|D|}}`, centred at `xk` with mesh size
parameter `Δk`. -/
def mesh {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (xk : Fin n → ℝ) (Δk : ℝ) :
    Set (Fin n → ℝ) :=
  {y | ∃ z : Fin p → ℕ, y = xk + Δk • (D *ᵥ (fun j => (z j : ℝ)))}

end GPSAnalysis.Core
