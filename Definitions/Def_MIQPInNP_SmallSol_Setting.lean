import Mathlib

namespace MIQPInNP.SmallSol

open scoped BigOperators Pointwise

/-! # Del Pia, Dey & Molinaro, *Mixed-integer quadratic programming is in NP* (arXiv:1407.4798v1)

The objects of §1 (p. 1), §1.1 (p. 2), §2.1 (p. 3) and §2.3 (p. 3). Data are rational, points are
real: a rational vector `v` is read as the real point `toReal v`. -/

/-- Bit-size ("complexity", §1.1, p. 2) of a rational number `a / b` in lowest terms, `b > 0`:
`1 + ⌈log₂(|a| + 1)⌉ + ⌈log₂(b + 1)⌉` (Schrijver's size: one sign bit and the binary lengths of the
numerator and of the denominator). -/
def bitSize (q : ℚ) : ℕ := 1 + Nat.size q.num.natAbs + Nat.size q.den

/-- Bit-size of a rational vector in `ℚⁿ`: `n` plus the sum of the bit-sizes of its entries. -/
def vecSize {n : ℕ} (v : Fin n → ℚ) : ℕ := n + ∑ i, bitSize (v i)

/-- Bit-size of a rational `m × n` matrix: `m n` plus the sum of the bit-sizes of its entries. -/
def matSize {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) : ℕ := m * n + ∑ i, ∑ j, bitSize (M i j)

/-- The complexity `φ` of the finite set of objects `{H, c, d, A, b}`: the sum of the complexities
of its constituents (§1.1, p. 2). -/
def instSize {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : ℕ :=
  matSize H + vecSize c + bitSize d + matSize A + vecSize b

/-- A rational vector read as a point of `ℝⁿ`. -/
def toReal {n : ℕ} (v : Fin n → ℚ) : Fin n → ℝ := fun i => (v i : ℝ)

/-- The quadratic form `x⊤ H x = ∑ᵢ ∑ⱼ xᵢ Hᵢⱼ xⱼ` (no symmetry of `H` is assumed). -/
def quadForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * (H i j : ℝ) * x j

/-- The quadratic function `𝒬(x) = x⊤ H x + c⊤ x + d` of (2) (p. 1; named `𝒬` on p. 6). -/
def quadVal {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ) (x : Fin n → ℝ) : ℝ :=
  quadForm H x + ∑ i, (c i : ℝ) * x i + (d : ℝ)

/-- The polyhedron `{x ∈ ℝⁿ : A x ≤ b}` of a rational system `A x ≤ b`. -/
def polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Set (Fin n → ℝ) :=
  {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)}

/-- `x ∈ ℤᵖ × ℝ^{n-p}`: the first `p` coordinates of `x` are integers. -/
def IsMixedInt {n : ℕ} (p : ℕ) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, (i : ℕ) < p → ∃ z : ℤ, x i = z

/-- The feasible set `𝓕(H, c, d, A, b)` of (2), p. 1: the real points `x` with
`x⊤ H x + c⊤ x + d ≤ 0`, `A x ≤ b` and `x ∈ ℤᵖ × ℝ^{n-p}`. -/
def feasSet {n m : ℕ} (p : ℕ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Set (Fin n → ℝ) :=
  {x | quadVal H c d x ≤ 0 ∧ x ∈ polyhedron A b ∧ IsMixedInt p x}

/-- The recession cone `rec(𝒞) = {x : A x ≤ 0}` of the polyhedron `𝒞 = {x : A x ≤ b}` (p. 6). -/
def recCone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Set (Fin n → ℝ) :=
  polyhedron A 0

/-- The polyhedron `{x : A x ≤ b}` is pointed: its lineality space `{x : A x = 0}` is `{0}`. -/
def IsPointedPoly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ i, ∑ j, (A i j : ℝ) * x j = 0) → x = 0

/-- The conic hull `cone(S)`: all non-negative real combinations of finitely many vectors of `S`. -/
def cone {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (Submodule.span NNReal S : Set (Fin n → ℝ))

/-- `int.cone(S)` (§2.1, p. 3): all combinations `∑ λⱼ rʲ` of finitely many `rʲ ∈ S` with
non-negative integer coefficients `λⱼ ∈ ℤ₊`. -/
def intCone {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (AddSubmonoid.closure S : Set (Fin n → ℝ))

/-- A set `K` (a cone) is pointed: it contains no line, i.e. `x ∈ K` and `-x ∈ K` force `x = 0`. -/
def IsPointedCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ K, -x ∈ K → x = 0

/-- `r` spans an extreme ray of the cone `K`: `r ∈ K`, `r ≠ 0`, and whenever `r = u + v` with
`u, v ∈ K`, the vector `u` is a non-negative multiple of `r`. -/
def IsExtremeRayOf {n : ℕ} (K : Set (Fin n → ℝ)) (r : Fin n → ℝ) : Prop :=
  r ∈ K ∧ r ≠ 0 ∧ ∀ u ∈ K, ∀ v ∈ K, u + v = r → ∃ t : ℝ, 0 ≤ t ∧ u = t • r

/-- The Euclidean norm `‖x‖ = (∑ᵢ xᵢ²)^{1/2}` (not Lean's sup norm on `Fin n → ℝ`). -/
noncomputable def euclidNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The hyperplane `𝓗 = {x : f⊤ x = 1}` of a rational vector `f`. -/
def hyperplane {n : ℕ} (f : Fin n → ℚ) : Set (Fin n → ℝ) :=
  {x | ∑ j, (f j : ℝ) * x j = 1}

end MIQPInNP.SmallSol
