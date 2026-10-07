import Mathlib

namespace GomoryGroup.Rel

open Matrix

variable {m n : ℕ}

/-- The basis `B` (the columns `α₁, …, α_m` of `A`), cast to a real matrix. -/
def Br (B : Matrix (Fin m) (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℝ :=
  B.map (fun z : ℤ => (z : ℝ))

/-- The nonbasic part `N` (the columns `α_{m+1}, …, α_{m+n}` of `A`), cast to a real matrix.
Column `j : Fin n` of `N` is the paper's `α_{m+1+j}`. -/
def Nr (N : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℝ :=
  N.map (fun z : ℤ => (z : ℝ))

/-- The Euclidean norm `‖v‖ = (∑ i, v i ^ 2)^{1/2}` of a real `m`-vector. -/
noncomputable def euclNorm (v : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- `A = (A′, I)`: after the rearrangement `A = (B, N)`, every unit vector `e_i` of `ℤ^m`
is a column of `B` or a column of `N`. -/
def HasUnitColumns (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ i : Fin m,
    (∃ j : Fin m, ∀ r : Fin m, B r j = if r = i then 1 else 0) ∨
    (∃ j : Fin n, ∀ r : Fin m, N r j = if r = i then 1 else 0)

/-- Feasibility for P1 (1) with right-hand side `β`: `B x_B + N x_N = β`, `x_B ≥ 0`, `x_N ≥ 0`,
with real `x`. -/
def IsLPFeasible (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (β : Fin m → ℝ) (xB : Fin m → ℝ) (xN : Fin n → ℝ) : Prop :=
  Br B *ᵥ xB + Nr N *ᵥ xN = β ∧ 0 ≤ xB ∧ 0 ≤ xN

/-- The set of costs `c_B x_B + c_N x_N` of the feasible points of P1 with right-hand side `β`. -/
def lpValues (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (β : Fin m → ℝ) : Set ℝ :=
  {z | ∃ (xB : Fin m → ℝ) (xN : Fin n → ℝ), IsLPFeasible B N β xB xN ∧ z = cB ⬝ᵥ xB + cN ⬝ᵥ xN}

/-- Feasibility for P2: `x` integer and nonnegative (`ℕ`-valued) with `B x_B + N x_N = b`. -/
def IsIPFeasible (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (xB : Fin m → ℕ) (xN : Fin n → ℕ) : Prop :=
  B *ᵥ (fun i => (xB i : ℤ)) + N *ᵥ (fun j => (xN j : ℤ)) = b

/-- The cost `c_B x_B + c_N x_N` of an integer point. -/
def ipCost (cB : Fin m → ℝ) (cN : Fin n → ℝ) (xB : Fin m → ℕ) (xN : Fin n → ℕ) : ℝ :=
  cB ⬝ᵥ (fun i => (xB i : ℝ)) + cN ⬝ᵥ (fun j => (xN j : ℝ))

/-- The set of costs of the feasible points of P2 with right-hand side `b`. -/
def ipValues (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) : Set ℝ :=
  {z | ∃ (xB : Fin m → ℕ) (xN : Fin n → ℕ), IsIPFeasible B N b xB xN ∧ z = ipCost cB cN xB xN}

/-- `(x_B, x_N)` is an optimal solution of P2: feasible, and no feasible point costs more. -/
def IsIPOptimal (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (xB : Fin m → ℕ) (xN : Fin n → ℕ) : Prop :=
  IsIPFeasible B N b xB xN ∧
    ∀ (xB' : Fin m → ℕ) (xN' : Fin n → ℕ), IsIPFeasible B N b xB' xN' →
      ipCost cB cN xB' xN' ≤ ipCost cB cN xB xN

/-- The relative cost `c*_{m+1+j} = c_{m+1+j} − c_B B⁻¹ α_{m+1+j}` of the nonbasic column `j`. -/
noncomputable def reducedCost (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) : Fin n → ℝ :=
  fun j => cN j - cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun r => (N r j : ℝ)))

/-- Feasibility for the group problem (4): `y ∈ ℕ^n` with `Σ ᾱ_{i+m} y_i = b̄` in `M(I)/M(B)`,
i.e. `b − N y` lies in the lattice `𝔏_B = M(B) = B ℤ^m`. -/
def IsGroupFeasible (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (y : Fin n → ℕ) : Prop :=
  ∃ k : Fin m → ℤ, b - N *ᵥ (fun j => (y j : ℤ)) = B *ᵥ k

/-- The objective `Σ_j c*_{m+1+j} y_j` of the group problem (4). -/
noncomputable def groupObj (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (y : Fin n → ℕ) : ℝ :=
  ∑ j, reducedCost B N cB cN j * (y j : ℝ)

/-- The set of objective values of the feasible points of the group problem (4) for `b`. -/
noncomputable def groupValues (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) : Set ℝ :=
  {z | ∃ y : Fin n → ℕ, IsGroupFeasible B N b y ∧ z = groupObj B N cB cN y}

/-- `y` is an optimal solution of the group problem (4) for `b`. -/
def IsGroupOptimal (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (y : Fin n → ℕ) : Prop :=
  IsGroupFeasible B N b y ∧
    ∀ y' : Fin n → ℕ, IsGroupFeasible B N b y' → groupObj B N cB cN y' ≤ groupObj B N cB cN y

/-- The cone `K^B = {β ∈ ℝ^m : B⁻¹ β ≥ 0}` of right-hand sides for which `B` is a feasible basis. -/
noncomputable def basisCone (B : Matrix (Fin m) (Fin m) ℤ) : Set (Fin m → ℝ) :=
  {β | 0 ≤ (Br B)⁻¹ *ᵥ β}

/-- The reduced cone `K^B(d)`: the points `β` whose closed Euclidean ball of radius `d`
lies inside `K^B`. -/
noncomputable def reducedCone (B : Matrix (Fin m) (Fin m) ℤ) (d : ℝ) : Set (Fin m → ℝ) :=
  {β | ∀ v : Fin m → ℝ, euclNorm (v - β) ≤ d → v ∈ basisCone B}

/-- `l = max_j ‖α_{m+1+j}‖`, the largest Euclidean length of a nonbasic column
(`0` when `n = 0`). -/
noncomputable def ell (N : Matrix (Fin m) (Fin n) ℤ) : ℝ :=
  ⨆ j : Fin n, euclNorm (fun r => (N r j : ℝ))

/-- `D = |det B|`. -/
def detD (B : Matrix (Fin m) (Fin m) ℤ) : ℕ :=
  B.det.natAbs

end GomoryGroup.Rel
