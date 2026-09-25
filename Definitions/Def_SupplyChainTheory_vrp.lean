import Mathlib

namespace SupplyChainTheory

/-! ### The vehicle routing problem with unit demands, Sect. 11.1 and 11.4.1 -/

/-- Symmetric nonnegative distances on the nodes `Fin (n+1)` (depot `0`, customers `1, …, n`)
with `cᵢᵢ = 0` and the triangle inequality. -/
structure VRPMetric {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : Prop where
  symm : ∀ i j, c i j = c j i
  nonneg : ∀ i j, 0 ≤ c i j
  refl : ∀ i, c i i = 0
  triangle : ∀ i j k, c i j ≤ c i k + c k j

/-- The length of the closed walk through the nodes of a list in order and back to its start. -/
def closedLength {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (L : List (Fin (n + 1))) : ℝ :=
  (List.zipWith c L (L.rotate 1)).sum

/-- The length of a route: from the depot through the customers of `L` in order and back. -/
def routeCost {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (L : List (Fin (n + 1))) : ℝ :=
  closedLength c (0 :: L)

/-- A VRP solution with unit demands and vehicle capacity `C`: a family of routes, each a
nonempty list of at most `C` customers, together covering every customer exactly once. -/
def IsVRPSolution {n : ℕ} (C : ℕ) (R : List (List (Fin (n + 1)))) : Prop :=
  (∀ L ∈ R, L ≠ [] ∧ L.length ≤ C ∧ (0 : Fin (n + 1)) ∉ L)
    ∧ (R.flatMap id).Nodup ∧ ∀ v : Fin (n + 1), v ≠ 0 → v ∈ R.flatMap id

/-- The total length of a VRP solution. -/
def solutionCost {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (R : List (List (Fin (n + 1)))) : ℝ :=
  (R.map (routeCost c)).sum

/-- `z*`, the optimal VRP objective with unit demands and capacity `C`. -/
noncomputable def vrpOpt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (C : ℕ) : ℝ :=
  sInf {z | ∃ R, IsVRPSolution C R ∧ z = solutionCost c R}

/-- A TSP tour through the depot and all customers, as the list of customers in visiting order. -/
def IsCustomerTour {n : ℕ} (L : List (Fin (n + 1))) : Prop :=
  L.Nodup ∧ (0 : Fin (n + 1)) ∉ L ∧ ∀ v : Fin (n + 1), v ≠ 0 → v ∈ L

/-- `z_T`, the length of the optimal TSP tour through all the nodes. -/
noncomputable def tspOpt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  sInf {z | ∃ L, IsCustomerTour L ∧ z = routeCost c L}

/-- `c̄ = (1/n) ∑ᵢ c₀ᵢ`, the average distance from the depot to the customers. -/
noncomputable def avgDepotDist {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin (n + 1), c 0 i) / n
end SupplyChainTheory
