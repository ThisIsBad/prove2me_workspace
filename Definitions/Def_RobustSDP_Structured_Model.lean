import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- An affine matrix-valued map given by its coefficients (El Ghaoui–Oustry–Lebret 1998, (1),
p. 33, and §2.2, p. 35): `affineMap A x = A₀ + ∑ᵢ xᵢ Aᵢ`, where the coefficient `A (i+1)` is the
paper's `A_{i+1}` multiplying the `i`-th coordinate of `x : Fin m → ℝ` (0-based). Used both for
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`) and for `R(x) = R₀ + ∑ xᵢ Rᵢ` (`q × n`). -/
def affineMap {m r c : ℕ} (A : Fin (m + 1) → Matrix (Fin r) (Fin c) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin r) (Fin c) ℝ :=
  A 0 + ∑ i : Fin m, x i • A i.succ

/-- The linear-fractional representation (5), p. 35:
`F(x, Δ) = F(x) + L Δ (I − DΔ)⁻¹ R(x) + R(x)ᵀ (I − ΔᵀDᵀ)⁻¹ Δᵀ Lᵀ`, written for given values
`Fx = F(x)` (`n × n`) and `Rx = R(x)` (`q × n`), with `L : n × p`, `D : q × p`, `Δ : p × q`.
Mathlib's `⁻¹` returns `0` on a singular matrix, so this expression is only meaningful where
`det (1 - D * Δ) ≠ 0`; every use states that guard next to it. -/
noncomputable def lfr {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ) (Rx : Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ) (Δ : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Fx + L * Δ * (1 - D * Δ)⁻¹ * Rx + Rxᵀ * (1 - Δᵀ * Dᵀ)⁻¹ * Δᵀ * Lᵀ

/-- The robust feasible set (2), p. 35, for the perturbation model `(F(·), R(·), L, D, 𝒟, ρ)`:
`x` is robustly feasible iff for every `Δ ∈ 𝒟` with spectral norm `‖Δ‖ ≤ ρ`, `F(x, Δ)` is well
defined (`det (I − DΔ) ≠ 0`) and `F(x, Δ) ⪰ 0`. The norm is the largest singular value
(`Matrix.Norms.L2Operator`), and `⪰ 0` is `Matrix.PosSemidef` (symmetric positive semidefinite).
`𝒟` is an arbitrary linear subspace of `ℝ^{p×q}` (§3.2, p. 37). -/
def robustFeasibleSet {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ →
    (1 - D * Δ).det ≠ 0 ∧ (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosSemidef}

/-- The set `𝓑` of scaling triples associated with the subspace `𝒟` (§3.2, (11), p. 37),
**corrected** as the proof of Lemma 3.2 requires: triples
`(S, T, G) ∈ ℝ^{p×p} × ℝ^{q×q} × ℝ^{p×q}` with `S Δ = Δ T` and `G Δᵀ = −Δ Gᵀ` for every
`Δ ∈ 𝒟`. (The printed (11) takes `G ∈ ℝ^{q×p}` with `GΔ = −ΔᵀGᵀ`; with that shape the products
`LG`, `DG` of (13) are undefined. For square skew-symmetric `G` and symmetric `Δ` the two
conditions coincide.) -/
def scalingSet {p q : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) :
    Set (Matrix (Fin p) (Fin p) ℝ × Matrix (Fin q) (Fin q) ℝ × Matrix (Fin p) (Fin q) ℝ) :=
  {STG | ∀ Δ ∈ 𝒟, STG.1 * Δ = Δ * STG.2.1 ∧ STG.2.2 * Δᵀ = -(Δ * STG.2.2ᵀ)}

/-- The `(n + q) × (n + q)` block matrix of the SDP of Theorem 3.2, p. 37, in the variables
`(x, S, T, G)`, **corrected** (see `scalingSet`), written for given values `Fx = F(x)`,
`Rx = R(x)`:
`[[F(x) − LSLᵀ, R(x)ᵀ − LSDᵀ + LG], [R(x) − DSLᵀ + GᵀLᵀ, ρ⁻²T − DSDᵀ + DG + GᵀDᵀ]]`
(`Matrix.fromBlocks A B C D` has `B` top-right and `C` bottom-left). At `ρ = 1` it is the
corrected matrix (13) of Lemma 3.2. -/
noncomputable def structuredLMI {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ)
    (Rx : Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (ρ : ℝ) : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ :=
  fromBlocks (Fx - L * S * Lᵀ) (Rxᵀ - L * S * Dᵀ + L * G) (Rx - D * S * Lᵀ + Gᵀ * Lᵀ)
    ((ρ ^ 2)⁻¹ • T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)

/-- Horizontal block concatenation `[L₁ … L_m]` of `n × rᵢ` matrices (§5.8, p. 47), with the
column index `⟨i, k⟩ : Σ i, Fin (r i)` meaning column `k` of block `i`. -/
def blockRow {m n : ℕ} {r : Fin m → ℕ} (Ls : (i : Fin m) → Matrix (Fin n) (Fin (r i)) ℝ) :
    Matrix (Fin n) (Σ i, Fin (r i)) ℝ :=
  Matrix.of fun a b => Ls b.1 a b.2

/-- Vertical block concatenation `[R₁; …; R_m]` of `rᵢ × n` matrices (§5.8, p. 47), with the
row index `⟨i, k⟩ : Σ i, Fin (r i)` meaning row `k` of block `i`. -/
def blockCol {m n : ℕ} {r : Fin m → ℕ} (Rs : (i : Fin m) → Matrix (Fin (r i)) (Fin n) ℝ) :
    Matrix (Σ i, Fin (r i)) (Fin n) ℝ :=
  Matrix.of fun b a => Rs b.1 b.2 a

end RobustSDP.Structured
