import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

variable {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The cumulative supply `S_{ijt}` at base `j` through period `t` in the stock allocation
model, for regular shipments `y j t' = y^r_{ijt'}` (constraint (10.16), p. 236):
`S_{ijt} = S̃_{ij(T^r_{ij}-1)} + Σ_{t'=0}^{t - T^r_{ij}} y^r_{ijt'}`,
meaningful for `t = T^r_{ij}, …, T^r_{ij} + T_{i0}`. -/
def samStock (M : ItemModel J Ω P) (y : J → ℕ → ℕ) (j : J) (t : ℕ) : ℤ :=
  M.baseSupply j (M.Tr j - 1) + ∑ t' ∈ Finset.range (t - M.Tr j + 1), (y j t' : ℤ)

/-- Feasibility for `SAM_i` (10.15)–(10.17), p. 236: the shipments `y j t = y^r_{ijt}` are
nonnegative integers (the type `ℕ`), and the cumulative quantity shipped from the depot
warehouse through period `t` never exceeds the cumulative depot supply,
`S̃_{i0t} ≥ Σ_{j∈J} Σ_{t'=0}^{t} y^r_{ijt'}` for `t = 0, …, T_{i0}`. The values `y j t` for
`t > T_{i0}` do not enter the model. -/
def SAMFeasible [Fintype J] (M : ItemModel J Ω P) (y : J → ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t ≤ M.T0 → ∑ j, ∑ t' ∈ Finset.range (t + 1), (y j t' : ℤ) ≤ M.depotSupply t

/-- The objective (10.14) of `SAM_i`, p. 236:
`Σ_{j∈J} { Σ_{t=T^r_{ij}}^{T^r_{ij}+T_{i0}} G_{ijt}(S_{ijt}) + Q_{ij}(S_{ij(T^r_{ij}+T_{i0})}) }`. -/
noncomputable def samObjective [Fintype J] (M : ItemModel J Ω P) (y : J → ℕ → ℕ) : ℝ :=
  ∑ j, ((∑ t ∈ Finset.Icc (M.Tr j) (M.Tr j + M.T0), M.G j t (samStock M y j t))
    + M.Q j (samStock M y j (M.Tr j + M.T0)))

/-- `y` is an optimal solution of `SAM_i`: feasible, with objective value at most that of
every feasible solution. -/
def IsSAMOptimal [Fintype J] (M : ItemModel J Ω P) (y : J → ℕ → ℕ) : Prop :=
  SAMFeasible M y ∧ ∀ y' : J → ℕ → ℕ, SAMFeasible M y' → samObjective M y ≤ samObjective M y'

/-- Feasibility for the multi-item problem `SAM` (10.11)–(10.13), p. 236, over a set `I`
of items, item `i` having data `M i`: each item's shipments satisfy that item's constraints. -/
def MultiSAMFeasible {I : Type*} [Fintype J] (M : I → ItemModel J Ω P)
    (y : I → J → ℕ → ℕ) : Prop :=
  ∀ i, SAMFeasible (M i) (y i)

/-- The objective (10.10) of `SAM`, p. 236: the sum over items of the `SAM_i` objectives. -/
noncomputable def multiSamObjective {I : Type*} [Fintype I] [Fintype J]
    (M : I → ItemModel J Ω P) (y : I → J → ℕ → ℕ) : ℝ :=
  ∑ i, samObjective (M i) (y i)

/-- `y` is an optimal solution of the multi-item problem `SAM` (10.10)–(10.13). -/
def IsMultiSAMOptimal {I : Type*} [Fintype I] [Fintype J] (M : I → ItemModel J Ω P)
    (y : I → J → ℕ → ℕ) : Prop :=
  MultiSAMFeasible M y ∧
    ∀ y' : I → J → ℕ → ℕ, MultiSAMFeasible M y' → multiSamObjective M y ≤ multiSamObjective M y'

end ServiceParts.RealTime
