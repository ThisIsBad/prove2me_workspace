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

/-- `M1, M2` index the basic `u`- and `v`-components of a basis of `(8.1)` in which `α`, `β`, `u0`
and `v0` are basic (Balas §8.1, Lemma 8.2, p. 98: "let the basic components of `u` and `v` be
indexed by `M1` and `M2`"). A basis of the `(2n+3)`-row equality system of `(8.1)` is a set of
`2n+3` linearly independent columns; with the `n+1` columns of the free variables `α, β` and the
two columns of `u0, v0` basic, this means: `|M1| + |M2| = n`, and the columns of
`α, β, u0, v0, u_{M1}, v_{M2}` are linearly independent, i.e. the homogeneous equality system of
`(8.1)` (normalization right-hand side `0`) has only the trivial solution among vectors supported
on these columns. -/
def IsCGLPKBasis {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (k : Fin n) (M1 M2 : Finset M) : Prop :=
  M1.card + M2.card = n ∧
    ∀ (dα : Fin n → ℝ) (du : M → ℝ) (du0 : ℝ) (dv : M → ℝ) (dv0 dβ : ℝ),
      (∀ i, dα i - (∑ ρ, du ρ * Atil ρ i) + (if i = k then du0 else 0) = 0) →
      (∀ i, dα i - (∑ ρ, dv ρ * Atil ρ i) - (if i = k then dv0 else 0) = 0) →
      -dβ + ∑ ρ, du ρ * btil ρ = 0 → -dβ + (∑ ρ, dv ρ * btil ρ) + dv0 = 0 →
      (∑ ρ, du ρ) + du0 + (∑ ρ, dv ρ) + dv0 = 0 →
      (∀ ρ ∉ M1, du ρ = 0) → (∀ ρ ∉ M2, dv ρ = 0) →
      dα = 0 ∧ du = 0 ∧ du0 = 0 ∧ dv = 0 ∧ dv0 = 0 ∧ dβ = 0

/-- Row `ρ` of `Ãx ≥ b̃` is the nonnegativity constraint `x_j ≥ 0` of variable `j`
(`Ã_ρ = e_j`, `b̃_ρ = 0`). Balas §8 (p. 97-99) takes `Ã` to be the `(m+p+n)`-row matrix whose
last `n` rows are `x ≥ 0`, and identifies such a row with the variable it bounds (its surplus is
`x_j` itself); this predicate makes that identification explicit for an abstract row type. -/
def IsNonnegRow {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ρ : M)
    (j : Fin n) : Prop :=
  Atil ρ = Pi.single j 1 ∧ btil ρ = 0

/-- The standing assumption of Balas Ch. 8 (p. 97): the LP relaxation `Ãx ≥ b̃` of the mixed 0-1
program contains the rows `x_j ≥ 0` for every variable `j` and `-x_j ≥ -1` for every 0-1
variable `j ∈ N'` (`Ã = [A; -I_p 0; I_n]`, `b̃ = (b; -e; 0)`). -/
def IsMixedZeroOneSystem {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (Nprime : Finset (Fin n)) : Prop :=
  (∀ j : Fin n, ∃ ρ : M, IsNonnegRow Atil btil ρ j) ∧
    ∀ j ∈ Nprime, ∃ ρ : M, Atil ρ = -Pi.single j 1 ∧ btil ρ = -1

open Classical in
/-- `α¹_i := uÃ_i`, where the sum runs over the rows of `Ãx ≥ b̃` *other than* the
nonnegativity rows `x_i ≥ 0` (Theorem 6.4, Balas §6, restated locally): in the strengthening
formula the multipliers of `x ≥ 0` are the slack of `α ≥ uÃ`, not part of `uÃ`. (Including those
rows would make `α¹_i = α_i + u0[i=k]` and the strengthening void.) -/
noncomputable def Alpha1 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (u : M → ℝ) (i : Fin n) : ℝ :=
  ∑ ρ, if IsNonnegRow Atil btil ρ i then 0 else u ρ * Atil ρ i

open Classical in
/-- `α²_i := vÃ_i`, the sum running over the rows other than the nonnegativity rows `x_i ≥ 0`
(Theorem 6.4, restated locally). -/
noncomputable def Alpha2 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (v : M → ℝ) (i : Fin n) : ℝ :=
  ∑ ρ, if IsNonnegRow Atil btil ρ i then 0 else v ρ * Atil ρ i

/-- `m_i := (α²_i - α¹_i)/(u0+v0)` (Theorem 6.4, restated locally). -/
noncomputable def MBar {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (i : Fin n) : ℝ :=
  (Alpha2 Atil btil v i - Alpha1 Atil btil u i) / (u0 + v0)

/-- The strengthened lift-and-project cut coefficients `γ` of Theorem 6.4 (Balas–Jeroslow
monoidal strengthening, restated locally): `γ_i = min{α¹_i + u0⌈m_i⌉, α²_i - v0⌊m_i⌋}` for `i` in
the 0-1 index set `N'`, `γ_i = α_i` otherwise. -/
noncomputable def Gamma {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (Nprime : Finset (Fin n))
    (alpha : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ Nprime then
    min (Alpha1 Atil btil u i + u0 * ⌈MBar Atil btil u u0 v v0 i⌉)
      (Alpha2 Atil btil v i - v0 * ⌊MBar Atil btil u u0 v v0 i⌋)
  else alpha i

end Disjunctive.CutCorrespondence
