import Mathlib

namespace SupplyChainTheory

/-! ### The UFLP and its relaxations, Sect. 8.2 -/

/-- (8.3): the UFLP cost `∑ⱼ fⱼ xⱼ + ∑ᵢ ∑ⱼ hᵢ cᵢⱼ yᵢⱼ` of a location vector `x` and an assignment `y`. -/
def uflpCost {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) : ℝ :=
  ∑ j, f j * x j + ∑ i, ∑ j, h i * c i j * y i j

/-- (8.4)-(8.7): feasibility for (UFLP). -/
def UFLPFeasible {n m : ℕ} (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, ∑ j, y i j = 1) ∧ (∀ i j, y i j ≤ x j) ∧ (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i j, 0 ≤ y i j)

/-- Feasibility for the LP relaxation (UFLP-P): (8.6) replaced by `0 ≤ xⱼ ≤ 1`. -/
def UFLPLPFeasible {n m : ℕ} (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, ∑ j, y i j = 1) ∧ (∀ i j, y i j ≤ x j) ∧ (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ (∀ i j, 0 ≤ y i j)

/-- `z*`, the optimal objective value of (UFLP). -/
noncomputable def uflpOpt {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) : ℝ :=
  sInf {z | ∃ x y, UFLPFeasible x y ∧ z = uflpCost h c f x y}

/-- `z_LP`, the optimal objective value of the LP relaxation (UFLP-P). -/
noncomputable def uflpLP {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) : ℝ :=
  sInf {z | ∃ x y, UFLPLPFeasible x y ∧ z = uflpCost h c f x y}

/-- (8.9): the objective of the Lagrangian subproblem (UFLP-LR_λ), constraints (8.4) relaxed. -/
def lagrObjective {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) : ℝ :=
  ∑ j, f j * x j + ∑ i, ∑ j, (h i * c i j - lam i) * y i j + ∑ i, lam i

/-- (8.10)-(8.12): feasibility for the Lagrangian subproblem. -/
def LagrFeasible {n m : ℕ} (x : Fin m → ℝ) (y : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, y i j ≤ x j) ∧ (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i j, 0 ≤ y i j)

/-- `z_LR(λ)`, the optimal value of (UFLP-LR_λ). -/
noncomputable def zLR {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) : ℝ :=
  sInf {z | ∃ x y, LagrFeasible x y ∧ z = lagrObjective h c f lam x y}

/-- (8.13): the benefit `βⱼ = ∑ᵢ min{0, hᵢ cᵢⱼ − λᵢ}` of opening facility `j`. -/
def benefit {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (lam : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i, min 0 (h i * c i j - lam i)

/-- (8.14): the location vector `x̄` of Theorem 8.1. -/
noncomputable def lagrX {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (j : Fin m) : ℝ :=
  if benefit h c lam j + f j < 0 then 1 else 0

/-- (8.15): the assignment `ȳ` of Theorem 8.1. -/
noncomputable def lagrY {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ)
    (lam : Fin n → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  if lagrX h c f lam j = 1 ∧ h i * c i j - lam i < 0 then 1 else 0

/-- `z_LR = max_λ z_LR(λ)`, the Lagrangian dual value (8.17), as a supremum. -/
noncomputable def zLRbest {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) : ℝ :=
  sSup (Set.range (zLR h c f))

/-! ### DUALOC primal-dual pairs, Sect. 8.2.4 -/

/-- PDP1 and PDP2 (p. 283) for a dual solution `v` and facility set `J⁺`, with `ĉᵢⱼ = hᵢ cᵢⱼ`. -/
def PDP {n m : ℕ} (chat : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (v : Fin n → ℝ)
    (Jp : Finset (Fin m)) : Prop :=
  (∀ j ∈ Jp, ∑ i, max 0 (v i - chat i j) = f j) ∧ (∀ i, ∃ j ∈ Jp, chat i j ≤ v i)

/-- `a` assigns every customer to a nearest facility of `J⁺` ((8.53): `j⁺(i) = argmin_{k ∈ J⁺} ĉᵢₖ`). -/
def NearestIn {n m : ℕ} (chat : Fin n → Fin m → ℝ) (Jp : Finset (Fin m)) (a : Fin n → Fin m) :
    Prop :=
  ∀ i, a i ∈ Jp ∧ ∀ k ∈ Jp, chat i (a i) ≤ chat i k

/-- (8.52): `x⁺`, the indicator of `J⁺`. -/
def primalX {m : ℕ} (Jp : Finset (Fin m)) (j : Fin m) : ℝ := if j ∈ Jp then 1 else 0

/-- (8.53): `y⁺`, the assignment to `j⁺(i)`. -/
def primalY {n m : ℕ} (a : Fin n → Fin m) (i : Fin n) (j : Fin m) : ℝ := if j = a i then 1 else 0

/-- Customer `i` violates the complementary slackness condition (8.51) under `(x⁺, y⁺, v)`. -/
def ViolatesCS {n m : ℕ} (chat : Fin n → Fin m → ℝ) (v : Fin n → ℝ) (Jp : Finset (Fin m))
    (a : Fin n → Fin m) (i : Fin n) : Prop :=
  ∃ j, max 0 (v i - chat i j) * (primalY a i j - primalX Jp j) ≠ 0

/-! ### Networks and the p-median problem, Sect. 8.3.2 -/

/-- A point of a network: a position `t ∈ [0, 1]` along the edge `(u, w)` of length `len`. The
distance from node `i` to it is `min{d(i, u) + t·len, d(i, w) + (1 − t)·len}`, `d` being the
shortest-path distance between nodes. -/
structure NetPoint (n : ℕ) where
  u : Fin n
  w : Fin n
  len : ℝ
  t : ℝ
  len_pos : 0 < len
  t_mem : t ∈ Set.Icc (0 : ℝ) 1

/-- The shortest-path distance from node `i` to the network point `x`. -/
def netDist {n : ℕ} (d : Fin n → Fin n → ℝ) (i : Fin n) (x : NetPoint n) : ℝ :=
  min (d i x.u + x.t * x.len) (d i x.w + (1 - x.t) * x.len)

/-- `c(i, X)`: the distance from `i` to the nearest of the points `X`. -/
noncomputable def nearestDist {n p : ℕ} (d : Fin n → Fin n → ℝ) (i : Fin n) (X : Fin p → NetPoint n) :
    ℝ :=
  sInf (Set.range (fun k => netDist d i (X k)))

/-- `c(i, S)`: the distance from node `i` to the nearest node of `S`. -/
noncomputable def nearestNodeDist {n : ℕ} (d : Fin n → Fin n → ℝ) (i : Fin n) (S : Finset (Fin n)) :
    ℝ :=
  sInf ((fun j => d i j) '' S)

/-! ### The p-center problem, Sect. 8.4.3 -/

/-- The optimal objective value of the (vertex) `p`-center problem (8.94)-(8.100): the least
radius `r` within which some set of `p` facilities covers every customer. -/
noncomputable def pCenterValue {n m : ℕ} (c : Fin n → Fin m → ℝ) (p : ℕ) : ℝ :=
  sInf {r | ∃ S : Finset (Fin m), S.card = p ∧ ∀ i, ∃ j ∈ S, c i j ≤ r}
end SupplyChainTheory
