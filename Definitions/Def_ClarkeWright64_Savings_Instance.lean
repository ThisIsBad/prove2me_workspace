import Mathlib
import Definitions.Def_SupplyChainTheory_vrp

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Formulation, pp. 568–569. A depot `P₀ = 0` and customers
`P₁, …, P_M` (the nonzero elements of `Fin (M+1)`), the distances `d y z`, the loads `q j`
(only the values at customers are used), and a fleet of `n + 1` truck classes: class `i` has
capacity `C i` and `x i` trucks are available. Class `i` is the paper's `C_{i+1}`, so the
paper's largest capacity `C_n` is `C (Fin.last n)`. Availabilities live in `ℕ∞` because the
paper makes `x₁` infinite. The paper's standing assumptions (symmetric `d`, `C₁ < ⋯ < C_n`,
`x₁ = ∞`) are hypotheses of the theorems, not fields. -/
structure Instance (M n : ℕ) where
  d : Fin (M + 1) → Fin (M + 1) → ℝ
  q : Fin (M + 1) → ℝ
  C : Fin (n + 1) → ℝ
  x : Fin (n + 1) → ℕ∞

variable {M n : ℕ}

/-- The cell value of the half matrix, p. 573: the saving `d_{0,y} + d_{0,z} − d_{y,z}` of cell
`(y:z)`. -/
def Instance.saving (I : Instance M n) (y z : Fin (M + 1)) : ℝ :=
  I.d 0 y + I.d 0 z - I.d y z

/-- The load of a run (the ordered list of customers a truck visits): `∑ q_j` over its
customers. -/
def Instance.runLoad (I : Instance M n) (r : List (Fin (M + 1))) : ℝ :=
  (r.map I.q).sum

/-- The total mileage of a family of runs: each run `[a₁, …, a_k]` is driven as the closed
route `P₀ P_{a₁} ⋯ P_{a_k} P₀`, of length `SupplyChainTheory.routeCost d [a₁, …, a_k]`. -/
def Instance.mileage (I : Instance M n) (runs : List (List (Fin (M + 1)))) : ℝ :=
  (runs.map (SupplyChainTheory.routeCost I.d)).sum

/-- "Allocate loads to trucks" (p. 568): every run load in the multiset is carried by a truck of
some class whose capacity it does not exceed, and no class is used more often than it has trucks
available. The pairing `κ` lists each load together with the class of its truck. -/
def Instance.FleetFeasible (I : Instance M n) (loads : Multiset ℝ) : Prop :=
  ∃ κ : Multiset (ℝ × Fin (n + 1)),
    κ.map Prod.fst = loads ∧ (∀ p ∈ κ, p.1 ≤ I.C p.2) ∧
      ∀ i : Fin (n + 1), ((κ.filter (fun p => p.2 = i)).card : ℕ∞) ≤ I.x i

/-- The Table II test, p. 573 (Tables II, IV, VI). For every capacity level `C_i`, the number
of runs whose load exceeds `C_i` (the "Allocated" entry of column "Over C_i") is at most the number
of trucks of capacity greater than `C_i`, i.e. of the classes `k > i` (the "Available" entry). The
column "Up to C₁" is not tested. -/
def Instance.TableIIOK (I : Instance M n) (loads : Multiset ℝ) : Prop :=
  ∀ i : Fin (n + 1),
    (((loads.filter (fun l => I.C i < l)).card : ℕ) : ℕ∞) ≤ ∑ k ∈ Finset.Ioi i, I.x k

end ClarkeWright64.Savings
