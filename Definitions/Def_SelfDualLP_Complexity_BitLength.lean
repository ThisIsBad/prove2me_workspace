import Mathlib

open Matrix

namespace SelfDualLP.Complexity

/-- Encoding size of an integer `v`: `1 + ⌈log₂(|v| + 1)⌉` (sign bit plus binary digits);
`Nat.size k = ⌈log₂(k + 1)⌉` is the number of binary digits of `k`. -/
def intSize (v : ℤ) : ℕ :=
  1 + Nat.size v.natAbs

/-- Encoding size of an integer vector of length `p`: `p + Σᵢ size(vᵢ)`. -/
def vecSize {p : ℕ} (v : Fin p → ℤ) : ℕ :=
  p + ∑ i, intSize (v i)

/-- Encoding size of an integer `m × n` matrix: `mn + Σᵢⱼ size(aᵢⱼ)`. -/
def matSize {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  m * n + ∑ i, ∑ j, intSize (A i j)

/-- The bit length `L` of integer LP data `(A, b, c)`: `size(A) + size(b) + size(c)`. -/
def bitLength {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ) : ℕ :=
  matSize A + vecSize b + vecSize c

/-- `b̄ = b − Ae` over the integers (8). -/
def bbarInt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Fin m → ℤ :=
  b - A *ᵥ (fun _ => 1)

/-- `c̄ = c − e` over the integers (8). -/
def cbarInt {n : ℕ} (c : Fin n → ℤ) : Fin n → ℤ :=
  c - fun _ => 1

/-- `z̄ = cᵀe + 1` over the integers (8). -/
def zbarInt {n : ℕ} (c : Fin n → ℤ) : ℤ :=
  (∑ j, c j) + 1

/-- The bit length of the data of (HLP) under (7): `A, b, c, b̄, c̄, z̄` and the right-hand
side `−(n + 1)` of row (4). -/
def hlpBitLength {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (c : Fin n → ℤ) :
    ℕ :=
  bitLength A b c + vecSize (bbarInt A b) + vecSize (cbarInt c) + intSize (zbarInt c) +
    intSize (-((n : ℤ) + 1))

/-- The real matrix `A` with integer entries. -/
def castMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℝ :=
  A.map (Int.cast : ℤ → ℝ)

/-- The real vector with integer entries. -/
def castVec {p : ℕ} (v : Fin p → ℤ) : Fin p → ℝ :=
  fun i => (v i : ℝ)

end SelfDualLP.Complexity
