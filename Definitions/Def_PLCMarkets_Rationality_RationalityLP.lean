import Mathlib
import Definitions.Def_PLCMarkets_Rationality_EquilibriumNetwork

namespace PLCMarkets.Rationality

namespace FisherMarket

variable {n g : ℕ}

/-! Section 4 of Vazirani–Yannakakis 2011 (pp. 10:8–10:9): the linear program built from a
reference price vector `p'` (meant to be positive equilibrium prices). The combinatorial data
of the LP — which segments are forced, flexible or undesirable, and the constants `unsold(j)` —
are those of `p'` (Section 3); the variables are new prices `p` and a flow `f` on the network `N`
of Section 3.2 with capacities that are linear in `p`, plus an edge `(t, s)` of unbounded
capacity. -/

/-- A point of the LP: prices `p_j` and a flow value `f_e` on every edge `e` of `N`:
`fsrc j` on `(s, j)`, `fmid j i` on `(j, i)` (parallel edges merged), `fsnk i` on `(i, t)`,
and `fts` on the added edge `(t, s)`. -/
structure LPPoint (n g : ℕ) where
  p : Fin g → ℝ
  fsrc : Fin g → ℝ
  fmid : Fin g → Fin n → ℝ
  fsnk : Fin n → ℝ
  fts : ℝ

open Classical in
/-- `spent(i)` written as a linear polynomial in the price variables `p`: the sum of
`amount(s) · p_j` over the segments `s` (of good `j`) that are forced for `i` at `p'`. -/
noncomputable def spentLP (M : FisherMarket n g) (p' : Fin g → ℝ) (i : Fin n)
    (p : Fin g → ℝ) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : M.Seg i => M.IsForcedSeg p' s), (M.segAmount s : ℝ) * p s.1

/-- `unspent(i) = e(i) − spent(i)` as a linear polynomial in `p`. -/
noncomputable def unspentLP (M : FisherMarket n g) (p' : Fin g → ℝ) (i : Fin n)
    (p : Fin g → ℝ) : ℝ :=
  (M.budget i : ℝ) - M.spentLP p' i p

open Classical in
/-- The capacity of the edge `(j, i)` of `N` as a linear polynomial in `p`: the sum of
`amount(s) · p_j` over `i`'s bounded segments `s` of good `j` that are flexible at `p'` (the
capacity is infinite when the unbounded segment of `f^i_j` is flexible at `p'`). -/
noncomputable def flexCapLP (M : FisherMarket n g) (p' : Fin g → ℝ) (j : Fin g) (i : Fin n)
    (p : Fin g → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (M.util i j).segs.length =>
      M.IsFlexibleSeg p' (⟨j, k⟩ : M.Seg i)),
    (M.segAmount (⟨j, k⟩ : M.Seg i) : ℝ) * p j

/-- The objective of the LP: `f_(t,s) + Σ_i spent(i)`, to be maximized. -/
noncomputable def lpObjective (M : FisherMarket n g) (p' : Fin g → ℝ) (z : LPPoint n g) : ℝ :=
  z.fts + ∑ i, M.spentLP p' i z.p

/-- The feasible region of the LP of Section 4 built from `p'`.

1. Capacity constraints on every edge other than `(t, s)`: `f_(s,j) ≤ unsold(j) · p_j`
   (`unsold(j)` is the constant computed at `p'`), `f_(j,i) ≤` the capacity of `(j, i)` (none
   when the unbounded segment of `f^i_j` is flexible at `p'`: infinite capacity), and
   `f_(i,t) ≤ unspent(i)`.
2. Flow conservation at `s`, at every good `j`, at every buyer `i`, and at `t`.
3. Bang-per-buck constraints for every buyer `i`, in terms of the segment classes at `p'`
   (`σ` of good `j`, `τ` of good `j'`, bounded or unbounded): two flexible segments satisfy
   `slope(σ) · p_{j'} = slope(τ) · p_j`; a flexible `σ` and a forced `τ` satisfy
   `slope(σ) · p_{j'} ≤ slope(τ) · p_j`; a flexible `σ` and an undesirable `τ` satisfy
   `slope(σ) · p_{j'} ≥ slope(τ) · p_j`.
4. `unspent(i) ≥ 0` for every buyer, `unsold(j) ≥ 0` for every good, and `Σ_j p_j = M`,
   the total money of the buyers.
5. Nonnegativity of every flow variable and every price. -/
def IsLPFeasible (M : FisherMarket n g) (p' : Fin g → ℝ) (z : LPPoint n g) : Prop :=
  -- 1. capacities
  (∀ j, z.fsrc j ≤ M.unsold p' j * z.p j) ∧
  (∀ j i, ¬ M.IsFlexibleTail p' i j → z.fmid j i ≤ M.flexCapLP p' j i z.p) ∧
  (∀ i, z.fsnk i ≤ M.unspentLP p' i z.p) ∧
  -- 2. conservation at s, at each good, at each buyer, at t
  z.fts = ∑ j, z.fsrc j ∧
  (∀ j, z.fsrc j = ∑ i, z.fmid j i) ∧
  (∀ i, ∑ j, z.fmid j i = z.fsnk i) ∧
  ∑ i, z.fsnk i = z.fts ∧
  -- 3. bang-per-buck constraints
  (∀ i, ∀ σ τ : M.Piece i, M.pieceBpb p' σ = M.flexBpb p' i → M.pieceBpb p' τ = M.flexBpb p' i →
      (M.pieceSlope σ : ℝ) * z.p τ.1 = (M.pieceSlope τ : ℝ) * z.p σ.1) ∧
  (∀ i, ∀ σ τ : M.Piece i, M.pieceBpb p' σ = M.flexBpb p' i → M.flexBpb p' i < M.pieceBpb p' τ →
      (M.pieceSlope σ : ℝ) * z.p τ.1 ≤ (M.pieceSlope τ : ℝ) * z.p σ.1) ∧
  (∀ i, ∀ σ τ : M.Piece i, M.pieceBpb p' σ = M.flexBpb p' i → M.pieceBpb p' τ < M.flexBpb p' i →
      (M.pieceSlope τ : ℝ) * z.p σ.1 ≤ (M.pieceSlope σ : ℝ) * z.p τ.1) ∧
  -- 4. unspent, unsold, total price
  (∀ i, 0 ≤ M.unspentLP p' i z.p) ∧
  (∀ j, 0 ≤ M.unsold p' j) ∧
  ∑ j, z.p j = ∑ i, (M.budget i : ℝ) ∧
  -- 5. nonnegativity
  (∀ j, 0 ≤ z.fsrc j) ∧ (∀ j i, 0 ≤ z.fmid j i) ∧ (∀ i, 0 ≤ z.fsnk i) ∧ 0 ≤ z.fts ∧
  (∀ j, 0 ≤ z.p j)

/-- `z` is an optimal solution of the LP built from `p'`: it is feasible and no feasible point has
a larger objective value. -/
def IsLPOptimal (M : FisherMarket n g) (p' : Fin g → ℝ) (z : LPPoint n g) : Prop :=
  M.IsLPFeasible p' z ∧ ∀ w, M.IsLPFeasible p' w → M.lpObjective p' w ≤ M.lpObjective p' z

end FisherMarket

end PLCMarkets.Rationality
