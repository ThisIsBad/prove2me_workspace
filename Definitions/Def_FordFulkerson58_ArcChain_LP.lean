import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network

namespace FordFulkerson58.ArcChain

variable {V E ι : Type*} [DecidableEq E]

/-- The columns of the constraint matrix `[A | I]` of (3), indexed by `Col N ⊕ E`: `Sum.inl s` is the
incidence column of the chain `C_s` (variable `x_s`), `Sum.inr r'` is the unit column of the slack
variable `x_{n+r'}`. `column N j r` is the entry in row `r`. -/
def column (N : Network V E ι) : Col N ⊕ E → E → ℝ
  | Sum.inl s, r => inc N r s
  | Sum.inr r', r => if r = r' then 1 else 0

/-- The objective coefficients of (2): `1` for every chain variable, `0` for every slack variable. -/
def cost (N : Network V E ι) : Col N ⊕ E → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

/-- Feasibility for (3): chain flows `x ≥ 0`, slacks `y ≥ 0` (the page's `x_{n+r}`), and for every arc
`r`, `∑_s a_rs x_s + x_{n+r} = b_r`. -/
def Feasible [Fintype ι] [Fintype E] (N : Network V E ι) (x : Col N → ℝ) (y : E → ℝ) : Prop :=
  (∀ s, 0 ≤ x s) ∧ (∀ r, 0 ≤ y r) ∧ ∀ r, ∑ s, inc N r s * x s + y r = N.b r

/-- The objective (2): the total flow `∑_s x_s`. -/
noncomputable def objective [Fintype ι] [Fintype E] (N : Network V E ι) (x : Col N → ℝ) : ℝ :=
  ∑ s, x s

/-- The basis matrix `B = (b_rj)` of a choice `β : E → Col N ⊕ E` of `m` columns `s₁, …, s_m`
(§2, p. 1779): its `i`-th column is the column `β i` of `[A | I]`. -/
def basisMatrix (N : Network V E ι) (β : E → Col N ⊕ E) : Matrix E E ℝ :=
  fun r i => column N (β i) r

/-- `z` is the basic feasible solution of the basis `β`: it vanishes off the basic columns, satisfies
every constraint of (3) with equality, and is non-negative. -/
def IsBasicFeasibleSolution [Fintype ι] [Fintype E] (N : Network V E ι) (β : E → Col N ⊕ E)
    (z : Col N ⊕ E → ℝ) : Prop :=
  (∀ j, j ∉ Set.range β → z j = 0) ∧ (∀ r, ∑ j, column N j r * z j = N.b r) ∧ ∀ j, 0 ≤ z j

/-- The simplex multipliers (4) of the basis `β`: for every basic column `j = β i`,
`∑_r α_r b_rj` equals the objective coefficient of `j` (`1` for a chain, `0` for a slack). -/
def IsSimplexMultiplier [Fintype E] (N : Network V E ι) (β : E → Col N ⊕ E) (α : E → ℝ) : Prop :=
  ∀ i, ∑ r, α r * basisMatrix N β r i = cost N (β i)

/-- The reduced cost of column `j` with respect to the multipliers `α`: its objective coefficient minus
`∑_r α_r` times its entries. For a chain column `C_s` this is `1 − ∑_r α_r a_rs`. -/
def reducedCost [Fintype E] (N : Network V E ι) (α : E → ℝ) (j : Col N ⊕ E) : ℝ :=
  cost N j - ∑ r, α r * column N j r

end FordFulkerson58.ArcChain
