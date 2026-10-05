import Mathlib

namespace Disjunctive.CutCorrespondence

/-- `(CGLP)_k`, eq. (8.1) (Balas §8, p. 97): the cut-generating LP for the disjunction
`-x_k ≥ 0 ∨ x_k ≥ 1`, with the normalization constraint `ue+u0+ve+v0=1`. `u,v` range over the
full row space `M` of `Ã` (which "has `m+p+n` components" per the book's own remark). -/
def IsCGLPKFeasible {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) : Prop :=
  (∀ i, α i - (∑ ρ, u ρ * Atil ρ i) + (if i = k then u0 else 0) = 0) ∧
    (∀ i, α i - (∑ ρ, v ρ * Atil ρ i) - (if i = k then v0 else 0) = 0) ∧
    -β + ∑ ρ, u ρ * btil ρ = 0 ∧ -β + (∑ ρ, v ρ * btil ρ) + v0 = 0 ∧
    (∑ ρ, u ρ) + u0 + (∑ ρ, v ρ) + v0 = 1 ∧ 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ u0 ∧ 0 ≤ v0

/-- A cut `αx ≥ β` is dominated by the LP relaxation `Ãx ≥ b̃` if it is implied by a nonnegative
combination of its constraints (Balas §8, p. 97, used in Lemma 8.1's proof: "αx ≥ β is a
nonnegative linear combination of the inequalities of `Ãx ≥ b̃`"). -/
def IsDominatedByLP {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (α : Fin n → ℝ) (β : ℝ) : Prop :=
  ∃ lam : M → ℝ, 0 ≤ lam ∧ (∀ i, α i = ∑ ρ, lam ρ * Atil ρ i) ∧ β ≤ ∑ ρ, lam ρ * btil ρ

/-- The feasible set of `(CGLP)_k`, as a subset of the bundled point space (Balas §8, p. 97:
`(8.1)` is bounded by the normalization constraint, so its extreme points are exactly its basic
solutions). -/
def CGLPKFeasibleSet {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (k : Fin n) : Set ((Fin n → ℝ) × (M → ℝ) × ℝ × (M → ℝ) × ℝ × ℝ) :=
  {w | IsCGLPKFeasible Atil btil k w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2}

/-- `(α,β,u,u0,v,v0)` is a basic solution to `(8.1)`, formalized as an extreme point of `(8.1)`'s
(bounded, by the normalization constraint) feasible polytope (Balas §8, p. 97). -/
def IsBasicCGLPKSolution {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ)
    (β : ℝ) : Prop :=
  (α, u, u0, v, v0, β) ∈ Set.extremePoints ℝ (CGLPKFeasibleSet Atil btil k)

/-- `α¹_i := uÃ_i + u0[i=k]` as in eq. (6.4) (restated locally from `06-lift-project-cuts`, using
the *full*, not row-restricted, multipliers, per that chunk's `Alpha1_64`). -/
def Alpha1 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (u : M → ℝ) (u0 : ℝ)
    (k i : Fin n) : ℝ :=
  (∑ ρ, u ρ * Atil ρ i) + (if i = k then u0 else 0)

/-- `α²_i := vÃ_i - v0[i=k]` as in eq. (6.4) (restated locally from `06-lift-project-cuts`'s
`Alpha2_64`). -/
def Alpha2 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (v : M → ℝ) (v0 : ℝ)
    (k i : Fin n) : ℝ :=
  (∑ ρ, v ρ * Atil ρ i) - (if i = k then v0 else 0)

/-- `m̄_k := (α²_k - α¹_k)/(u0+v0)` (restated locally from `06-lift-project-cuts`'s `mip_cut_lifting`,
Theorem 6.4). -/
noncomputable def MBar {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (u : M → ℝ) (u0 : ℝ)
    (v : M → ℝ) (v0 : ℝ) (k i : Fin n) : ℝ :=
  (Alpha2 Atil v v0 k i - Alpha1 Atil u u0 k i) / (u0 + v0)

/-- The strengthened lift-and-project cut coefficients `γ` of Theorem 6.4 (restated locally from
`06-lift-project-cuts`): `γ_i = min{α¹_i+u0⌈m̄_i⌉, α²_i-v0⌊m̄_i⌋}` for `i` in the 0-1 index set
`N'`, `γ_i = α_i` otherwise. -/
noncomputable def Gamma {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (u : M → ℝ) (u0 : ℝ)
    (v : M → ℝ) (v0 : ℝ) (k : Fin n) (Nprime : Finset (Fin n)) (alpha : Fin n → ℝ) (i : Fin n) :
    ℝ :=
  if i ∈ Nprime then
    min (Alpha1 Atil u u0 k i + u0 * ⌈MBar Atil u u0 v v0 k i⌉)
      (Alpha2 Atil v v0 k i - v0 * ⌊MBar Atil u u0 v v0 k i⌋)
  else alpha i

end Disjunctive.CutCorrespondence
