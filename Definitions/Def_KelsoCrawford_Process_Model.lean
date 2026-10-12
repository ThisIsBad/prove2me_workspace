import Mathlib

namespace KelsoCrawford.Process

/-- A job-matching market (Kelso–Crawford 1982, §2, p. 1486): `u i j s` is worker `i`'s utility of
working for firm `j` at salary `s`; `y j C` is firm `j`'s gross product when it hires the set `C`
of workers; `σ i j` is the starting (lowest) salary of worker `i` at firm `j`. -/
structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- Net profit `π^j(C; s^j) = y^j(C) − Σ_{i ∈ C} s_ij` of a firm with gross product `y`, hiring `C`
at the salary vector `s`. -/
def profit (y : Finset W → ℝ) (C : Finset W) (s : W → ℝ) : ℝ :=
  y C - ∑ i ∈ C, s i

/-- `C ∈ M^j(s^j)`: the set `C` maximizes profit at the salary vector `s` over all sets of
workers (problem (A), p. 1486). -/
def IsDemanded (y : Finset W → ℝ) (s : W → ℝ) (C : Finset W) : Prop :=
  ∀ C' : Finset W, profit y C' s ≤ profit y C s

/-- Gross substitutes (GS), p. 1486, for one firm, over the set `S` of admissible salary
vectors: if `C ∈ M(s)` and `s ≤ s'` (both in `S`), there is `C' ∈ M(s')` containing every member
of `C` whose salary did not change. -/
def GrossSubstitutesOn (y : Finset W → ℝ) (S : Set (W → ℝ)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≤ s' → ∀ C, IsDemanded y s C →
    ∃ C', IsDemanded y s' C' ∧ C.filter (fun i => s' i = s i) ⊆ C'

/-- Every utility `u^i(j; ·)` is strictly increasing and continuous in the salary (p. 1486). -/
def Market.UtilityRegular (M : Market W F) : Prop :=
  ∀ i j, StrictMono (M.u i j) ∧ Continuous (M.u i j)

/-- (MP), p. 1486: `y^j(C ∪ {i}) − y^j(C) − σ_ij ≥ 0` for all `i, j` and all `C ∌ i`. -/
def Market.MP (M : Market W F) : Prop :=
  ∀ i j (C : Finset W), i ∉ C →
    0 ≤ M.y j (insert i C) - M.y j C - M.σ i j

/-- (NFL), p. 1486: `y^j(∅) = 0` for every firm. -/
def Market.NFL (M : Market W F) : Prop := ∀ j, M.y j ∅ = 0

/-- The salaries firm `j` may offer worker `i` in the discrete market with unit `δ`:
`σ_ij, σ_ij + δ, σ_ij + 2δ, …`. -/
def Market.grid (M : Market W F) (δ : ℝ) (i : W) (j : F) : Set ℝ :=
  {r | ∃ k : ℕ, r = M.σ i j + k * δ}

/-- Salary vectors of firm `j` all of whose entries are permitted salaries. -/
def Market.gridVectors (M : Market W F) (δ : ℝ) (j : F) : Set (W → ℝ) :=
  {s | ∀ i, s i ∈ M.grid δ i j}

/-- An allocation (D1, p. 1488): every worker `i` is assigned to the firm `assign i` at the
salary `sal i`. -/
structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

/-- `C^j = {i | f(i) = j}`, the workers hired by firm `j`. -/
def Allocation.hired (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

/-- Individual rationality, D1 (1)–(2), p. 1488. -/
def Market.IsIR (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ profit (M.y j) (A.hired j) A.sal

/-- A firm `j`, a set `C` of workers and salaries `r` (with `r i ∈ R i j` for `i ∈ C`) strictly
improve upon `A`: (3) and (4) of p. 1488 both hold with strict inequality (D3). -/
def Market.CanStrictlyImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    profit (M.y j) (A.hired j) A.sal < profit (M.y j) C r

/-- A (discrete) core allocation, D3, p. 1488, with permitted salaries `R`: individually
rational, paying permitted salaries, and not strictly improvable by any coalition of one firm
and a set of workers using permitted salaries. -/
def Market.IsCore (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanStrictlyImprove R A

end KelsoCrawford.Process
