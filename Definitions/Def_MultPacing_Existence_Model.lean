import Mathlib

namespace MultPacing.Existence

/-- A pacing game (§3, p. 6): a finite set `N` of buyers, a finite set `G` of divisible goods,
valuations `v i j ≥ 0` and budgets `B i > 0`. -/
structure PacingGame (N G : Type*) where
  /-- valuation `v_ij` of buyer `i` for good `j` -/
  v : N → G → ℝ
  /-- budget `B_i` of buyer `i` -/
  B : N → ℝ
  v_nonneg : ∀ i j, 0 ≤ v i j
  B_pos : ∀ i, 0 < B i

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

/-- The highest paced bid `α_k v_kj` on good `j` among buyers `k ≠ i`; it is `0` when `i` is the
only buyer (a lone bidder pays nothing, p. 16). -/
noncomputable def highestOther (v : N → G → ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  if h : (Finset.univ.erase i).Nonempty then
    (Finset.univ.erase i).sup' h (fun k => α k * v k j)
  else 0

/-- Second price pacing equilibrium (Definition 2, p. 9). `α` are the pacing multipliers, `x i j`
the fraction of good `j` allocated to buyer `i`, and `p j` the per-unit price of good `j`; the spend
of buyer `i` on good `j` is `s_ij = p_j x_ij`. -/
structure IsSPPE (P : PacingGame N G) (α : N → ℝ) (x : N → G → ℝ) (p : G → ℝ) : Prop where
  /-- `α ∈ [0,1]^N` -/
  alpha_mem : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1
  /-- `x_ij ∈ [0,1]` -/
  alloc_mem : ∀ i j, x i j ∈ Set.Icc (0 : ℝ) 1
  /-- `∑_i x_ij ≤ 1` for every good `j` -/
  supply : ∀ j, ∑ i, x i j ≤ 1
  /-- equality when some buyer values good `j` -/
  full_alloc : ∀ j, (∃ i, 0 < P.v i j) → ∑ i, x i j = 1
  /-- a buyer with `x_ij > 0` has a (possibly tied) highest bid on `j` -/
  winner_top : ∀ i j, 0 < x i j → ∀ k, α k * P.v k j ≤ α i * P.v i j
  /-- second price: if `x_ij > 0` then `p_j` is the highest bid other than `i`'s -/
  second_price : ∀ i j, 0 < x i j → p j = highestOther P.v α i j
  /-- budget constraint `∑_j p_j x_ij ≤ B_i` -/
  budget : ∀ i, ∑ j, p j * x i j ≤ P.B i
  /-- no unnecessary pacing: a buyer with budget slack has `α_i = 1` -/
  no_unnecessary_pacing : ∀ i, ∑ j, p j * x i j < P.B i → α i = 1

end MultPacing.Existence
