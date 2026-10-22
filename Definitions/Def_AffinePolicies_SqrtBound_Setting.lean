import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

namespace AffinePolicies.SqrtBound

open Matrix

section AlgorithmA

variable {m : ℕ}

/-- The scaled sum `Σ_{j ∈ J} b_j / μ_j`. -/
noncomputable def scaledSum (μ : Fin m → ℝ) (J : Finset (Fin m)) (b : Fin m → ℝ) : ℝ :=
  ∑ j ∈ J, b j / μ j

/-- The state `(bᵏ, J₁ᵏ)` of Algorithm 𝒜 (Fig. 1) after `k` iterations with the choices
`u 1, …, u k` (steps 1, 2(c), 2(d)); `u 0` is never used. Step 2(d) is read as
`J₁ᵏ = {j ∈ J₁^{k−1} : b_jᵏ < μ_j}`. -/
noncomputable def algState (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) :
    ℕ → (Fin m → ℝ) × Finset (Fin m)
  | 0 => (0, Finset.univ)
  | k + 1 =>
    let s := algState μ u k
    let b' : Fin m → ℝ := fun j => if j ∈ s.2 then s.1 j + u (k + 1) j else s.1 j
    (b', s.2.filter (fun j => b' j < μ j))

/-- The vector `bᵏ` of Algorithm 𝒜 after `k` iterations. -/
noncomputable def bvec (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) : Fin m → ℝ :=
  (algState μ u k).1

/-- The index set `J₁ᵏ` of Algorithm 𝒜 after `k` iterations (`J₂ᵏ` is its complement). -/
noncomputable def J1 (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) : Finset (Fin m) :=
  (algState μ u k).2

/-- The test of the while loop (step 2): some `b ∈ U` has `Σ_{j ∈ J} b_j / μ_j > √m`. -/
def LoopCond (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (J : Finset (Fin m)) : Prop :=
  ∃ b ∈ U, Real.sqrt m < scaledSum μ J b

/-- Iteration `k + 1` of Algorithm 𝒜 is executed with choice `u (k + 1)`: the loop test holds
for `J₁ᵏ`, and `u (k + 1)` maximizes `Σ_{j ∈ J₁ᵏ} b_j / μ_j` over `b ∈ U` (steps 2, 2(b)). -/
def IsIteration (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) : Prop :=
  LoopCond U μ (J1 μ u k) ∧ u (k + 1) ∈ U ∧
    ∀ b ∈ U, scaledSum μ (J1 μ u k) b ≤ scaledSum μ (J1 μ u k) (u (k + 1))

/-- A complete run of Algorithm 𝒜 with exactly `K` iterations (steps 2 and 3): iterations
`1, …, K` are executed and the loop test fails for `J₁ᴷ`. -/
def IsRun (U : Set (Fin m → ℝ)) (μ : Fin m → ℝ) (K : ℕ) (u : ℕ → Fin m → ℝ) : Prop :=
  (∀ k < K, IsIteration U μ u k) ∧ ¬ LoopCond U μ (J1 μ u K)

/-- The output `β = u¹ + ⋯ + u^K` of Algorithm 𝒜 (step 4). -/
def betaSum (u : ℕ → Fin m → ℝ) (K : ℕ) : Fin m → ℝ :=
  ∑ k ∈ Finset.Icc 1 K, u k

end AlgorithmA

section Construction

variable {m n₂ : ℕ}

/-- The linear part of the affine policy of the proof of Theorem 4: column `j` is
`y*(βʲ) / μ_j` for `j ∈ J` and `0` otherwise, so `P b = Σ_{j ∈ J} (b_j / μ_j) y*(βʲ)`. -/
noncomputable def thmPolicyP (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (bstar : Fin m → Fin m → ℝ)
    (μ : Fin m → ℝ) (J : Finset (Fin m)) : Matrix (Fin n₂) (Fin m) ℝ :=
  Matrix.of fun i j => if j ∈ J then ys (bstar j) i / μ j else 0

/-- The constant part `ŷ = (2√m / K) Σ_{k=1}^{K} y*(uᵏ)` of the affine policy of the proof of
Theorem 4, display (48) (it is `0` when `K = 0`, the empty sum). -/
noncomputable def thmPolicyq (ys : (Fin m → ℝ) → Fin n₂ → ℝ) (u : ℕ → Fin m → ℝ) (K : ℕ) :
    Fin n₂ → ℝ :=
  (2 * Real.sqrt m / K) • ∑ k ∈ Finset.Icc 1 K, ys (u k)

end Construction

section KModel

variable {k l n₁ n₂ : ℕ}

/-- `(x, y)` is feasible for `Π^k_Adapt(U)`, displays (60)–(63): `k` uncertain right-hand sides
`b ∈ U ⊆ ℝ^k` and `l` (the paper's `m − k`) fixed right-hand sides `b⁰ ∈ ℝ^l`; `x ≥ 0` and, for
every `b ∈ U`, `y(b) ≥ 0`, `A₁ x + B₁ y(b) ≥ b` and `A₂ x + B₂ y(b) ≥ b⁰`. -/
def FeasibleK (A₁ : Matrix (Fin k) (Fin n₁) ℝ) (A₂ : Matrix (Fin l) (Fin n₁) ℝ)
    (B₁ : Matrix (Fin k) (Fin n₂) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ) (b0 : Fin l → ℝ)
    (U : Set (Fin k → ℝ)) (x : Fin n₁ → ℝ) (y : (Fin k → ℝ) → Fin n₂ → ℝ) : Prop :=
  0 ≤ x ∧ ∀ b ∈ U, 0 ≤ y b ∧ b ≤ A₁ *ᵥ x + B₁ *ᵥ y b ∧ b0 ≤ A₂ *ᵥ x + B₂ *ᵥ y b

/-- `z^k_Adapt(U)`, display (60), as an epigraph infimum. -/
noncomputable def zAdaptK (A₁ : Matrix (Fin k) (Fin n₁) ℝ) (A₂ : Matrix (Fin l) (Fin n₁) ℝ)
    (B₁ : Matrix (Fin k) (Fin n₂) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ) (b0 : Fin l → ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin k → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (y : (Fin k → ℝ) → Fin n₂ → ℝ),
    FeasibleK A₁ A₂ B₁ B₂ b0 U x y ∧ AffinePolicies.Simplex.CostLE c d U x y t}

/-- `z^k_Aff(U)`: the epigraph infimum of `Π^k_Adapt(U)` over affine policies `b ↦ P b + q`. -/
noncomputable def zAffK (A₁ : Matrix (Fin k) (Fin n₁) ℝ) (A₂ : Matrix (Fin l) (Fin n₁) ℝ)
    (B₁ : Matrix (Fin k) (Fin n₂) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ) (b0 : Fin l → ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (U : Set (Fin k → ℝ)) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (P : Matrix (Fin n₂) (Fin k) ℝ) (q : Fin n₂ → ℝ),
    FeasibleK A₁ A₂ B₁ B₂ b0 U x (AffinePolicies.Simplex.affinePolicy P q) ∧ AffinePolicies.Simplex.CostLE c d U x (AffinePolicies.Simplex.affinePolicy P q) t}

/-- `z(Π₂)`: the optimal value of the deterministic problem
`min cᵀx + dᵀy s.t. A₂ x + B₂ y ≥ b⁰, x, y ≥ 0` (PDF p. 33). -/
noncomputable def zDet (A₂ : Matrix (Fin l) (Fin n₁) ℝ) (B₂ : Matrix (Fin l) (Fin n₂) ℝ)
    (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ) (b0 : Fin l → ℝ) : ℝ :=
  sInf {t | ∃ (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ),
    0 ≤ x ∧ 0 ≤ y ∧ b0 ≤ A₂ *ᵥ x + B₂ *ᵥ y ∧ c ⬝ᵥ x + d ⬝ᵥ y ≤ t}

end KModel

end AffinePolicies.SqrtBound
