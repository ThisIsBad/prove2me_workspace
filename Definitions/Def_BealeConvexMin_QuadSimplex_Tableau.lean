import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-!
Beale (1955), §2, p. 174, eq. (2.3), and §3, p. 175, eq. (3.1): the state of the iteration for a
quadratic `C`.

There are `n` restricted variables, indexed by `Fin n` (index `j` is the paper's `x_{j+1}`),
and `N` nonbasic slots (the paper's `N = n - m`). Slot `0` of `Fin (N+1)` is the constant `z_0 = 1`; the nonbasic slot with index
`k : Fin N` is slot `k.succ` (the paper's `z_{k+1}`).
-/

/-- A tableau (§2, eq. (2.3); §3, eq. (3.1)).
* `lab k` says which variable occupies nonbasic slot `k.succ`: `some j` for the restricted
  variable `x_j`, `none` for a free variable (a linear function of the `x_j` with no sign
  restriction, p. 174).
* `row j` expresses the restricted variable `x_j` as `x_j = Σ_{l=0}^{N} row j l · z_l`
  (eq. (2.3), `a_h0 = row h 0`). Every restricted variable has a row; a nonbasic one has the unit
  row. Free variables have no row (p. 175: "it is not normally necessary to retain the equation
  defining a free variable once that variable has ceased to be nonbasic").
* `c` is the matrix `(c_kl)` of eq. (3.1), `C = Σ_{k,l} c_kl z_k z_l` with `z_0 = 1`. -/
structure Tableau (n N : ℕ) where
  lab : Fin N → Option (Fin n)
  row : Fin n → Fin (N + 1) → ℝ
  c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ

variable {n N : ℕ}

/-- `x_j` is basic: it occupies no nonbasic slot. -/
def IsBasic (T : Tableau n N) (j : Fin n) : Prop :=
  ∀ k : Fin N, T.lab k ≠ some j

/-- The labelling is consistent: no restricted variable occupies two slots, and the row of a
nonbasic restricted variable `x_j` in slot `k.succ` is the unit row `x_j = z_{k+1}`. -/
def LabelsConsistent (T : Tableau n N) : Prop :=
  (∀ k k' : Fin N, ∀ j : Fin n, T.lab k = some j → T.lab k' = some j → k = k') ∧
  ∀ (k : Fin N) (j : Fin n), T.lab k = some j → T.row j = Pi.single k.succ 1

/-- The ε-perturbation device (p. 174: "We ensure that the `a_h0` are always positive, and not
zero"), stated as a property of one tableau: every basic restricted variable is strictly positive
in the associated solution (`a_h0 = row h 0 > 0`). Nonbasic variables vanish in the associated
solution and are not constrained. -/
def BasicPositive (T : Tableau n N) : Prop :=
  ∀ j : Fin n, IsBasic T j → 0 < T.row j 0

/-- `s`, the number of nonbasic free variables (p. 174, after (2.3)). -/
def numFree (T : Tableau n N) : ℕ :=
  (Finset.univ.filter fun k : Fin N => T.lab k = none).card

/-- The set of restricted nonbasic variables. -/
def restrictedNonbasic (T : Tableau n N) : Set (Fin n) :=
  {j | ∃ k : Fin N, T.lab k = some j}

/-- Standard form (§3, p. 177): `C` contains no linear term in any free variable, i.e.
`c_k0 = 0` for every nonbasic slot `k` holding a free variable. -/
def IsStandardForm (T : Tableau n N) : Prop :=
  ∀ k : Fin N, T.lab k = none → T.c k.succ 0 = 0

end BealeConvexMin.QuadSimplex
