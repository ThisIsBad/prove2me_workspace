import Mathlib
import Definitions.Def_BassokSubstitution_Model

namespace BassokSubstitution

variable {N : ℕ}

/-- A candidate solution of the allocation linear program (3): `w j i` is the quantity of
product `j` allocated to demand class `i`, `u i` the shortage of class `i`, `v j` the leftover
stock of product `j`. -/
structure Allocation (N : ℕ) where
  w : Fin N → Fin N → ℝ
  u : Fin N → ℝ
  v : Fin N → ℝ

/-- Feasibility for the allocation LP (3b)–(3e) at stock `y` and demand `d`. Upward allocations
(product `j` to a class `i < j`) are forbidden arcs and are fixed to `0`. -/
def Allocation.Feasible (y d : Fin N → ℝ) (a : Allocation N) : Prop :=
  (∀ j i : Fin N, i < j → a.w j i = 0) ∧
  (∀ j i : Fin N, 0 ≤ a.w j i) ∧
  (∀ i : Fin N, 0 ≤ a.u i) ∧
  (∀ j : Fin N, 0 ≤ a.v j) ∧
  (∀ i : Fin N, a.u i + ∑ j ∈ Finset.Iic i, a.w j i = d i) ∧
  (∀ j : Fin N, a.v j + ∑ i, a.w j i = y j)

/-- Objective (3a): `∑_i ∑_{j ≤ i} a_{ji} w_{ji} + ∑_i s_i v_i - ∑_i π_i u_i`. -/
def Model.allocObjective (M : Model N) (a : Allocation N) : ℝ :=
  (∑ i, ∑ j ∈ Finset.Iic i, M.netRevenue j i * a.w j i) + (∑ i, M.s i * a.v i)
    - ∑ i, M.penalty i * a.u i

/-- `G(y, d)`: the optimal value of the allocation LP (3), i.e. the supremum of the objective
over all feasible allocations. -/
noncomputable def Model.G (M : Model N) (y d : Fin N → ℝ) : ℝ :=
  sSup (M.allocObjective '' {a : Allocation N | a.Feasible y d})

/-- Working state of Allocation Algorithm (A), on `ℕ`-indexed arrays: remaining stock `v`,
unmet demand `u`, and allocations `w j i` (product `j` to class `i`). -/
structure AlgState where
  v : ℕ → ℝ
  u : ℕ → ℝ
  w : ℕ → ℕ → ℝ

/-- The inner `While` loop of Algorithm (A) for class `i`, run for `n` steps starting at
product `j`: set `w_{ji} = min(u_i, v_j)`, subtract it from `u_i` and `v_j`, and move on to
product `j - 1`. -/
def innerLoop (i : ℕ) : ℕ → ℕ → AlgState → AlgState
  | 0, _, st => st
  | n + 1, j, st =>
      innerLoop i n (j - 1)
        { v := Function.update st.v j (st.v j - min (st.u i) (st.v j))
          u := Function.update st.u i (st.u i - min (st.u i) (st.v j))
          w := Function.update st.w j (Function.update (st.w j) i (min (st.u i) (st.v j))) }

/-- Algorithm (A) restricted to the subproblem whose cheapest-to-most-flexible product range
starts at product `k`: the state after classes `k, k+1, …, k+n-1` have been processed, class
`i` drawing on products `i, i-1, …, k` in that order. Initially `v = y`, `u = 0`, `w = 0`;
at class `i` the algorithm sets `u_i = d_i` and runs the inner loop from product `i`. -/
def runFrom (k : ℕ) (y d : ℕ → ℝ) : ℕ → AlgState
  | 0 => { v := y, u := fun _ => 0, w := fun _ _ => 0 }
  | n + 1 =>
      let st := runFrom k y d n
      innerLoop (k + n) (n + 1) (k + n) { st with u := Function.update st.u (k + n) (d (k + n)) }

/-- Extend a vector on `Fin N` by `0` to all of `ℕ`. -/
def extend (f : Fin N → ℝ) : ℕ → ℝ :=
  fun n => if h : n < N then f ⟨n, h⟩ else 0

/-- The allocation produced by Algorithm (A) (Figure 1) on the full problem with stock `y`
and demand `d`: classes `1, …, N` are processed in order, class `i` served first from
product `i`, then from `i-1, …, 1`. -/
def greedyAllocation (y d : Fin N → ℝ) : Allocation N :=
  let st := runFrom 0 (extend y) (extend d) N
  { w := fun j i => st.w j.val i.val
    u := fun i => st.u i.val
    v := fun j => st.v j.val }

/-- The subproblem shortage `S^k_j` (paper's notation, with `k` the first product of the
subproblem): the unmet demand of class `j` when Algorithm (A) is run on classes `k, …, j`
using products `k, …, j` only. Both indices are 0-based; `k` is a natural number so that
`k + 1` needs no bound. Junk value `0` when `j < k` (never used). -/
def shortage (y d : Fin N → ℝ) (k : ℕ) (j : Fin N) : ℝ :=
  if k ≤ j.val then (runFrom k (extend y) (extend d) (j.val + 1 - k)).u j.val else 0

/-- The vector condition `S⃗^k_{a,n} = 0`: `S^k_m = 0` for every class `m` with
`a ≤ m ≤ n` (0-based). It holds vacuously when the range is empty. The paper's
`S⃗^k_{a,n} > 0` is its negation (shortages are nonnegative). -/
def ShortVecZero (y d : Fin N → ℝ) (k a n : ℕ) : Prop :=
  ∀ m : Fin N, a ≤ m.val → m.val ≤ n → shortage y d k m = 0

end BassokSubstitution
