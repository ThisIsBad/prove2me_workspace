import Mathlib

namespace DecentralizedDistribution.FirstBest

/-- The distribution system of Anupindi–Bassok–Zemel (2001), §3, pp. 353–354.
Retailers are `Fin N`, centralized warehouses are `Fin W`; a location is a retailer
(`Sum.inl n`) or a warehouse (`Sum.inr w`).
* `c n`, `r n`, `v n`: unit cost, unit revenue, unit salvage value of retailer `n`;
* `cw w`, `vw w`: purchasing cost and salvage value at warehouse `w`;
* `t i n`: per-unit additional shipping/handling/discounting cost of meeting demand at
  retailer `n` from location `i`;
* `β i n`: the (deterministic) fraction of customers at retailer `n` who accept service
  out of location `i`, with `0 ≤ β i n ≤ 1`. -/
structure System (N W : ℕ) where
  c : Fin N → ℝ
  r : Fin N → ℝ
  v : Fin N → ℝ
  cw : Fin W → ℝ
  vw : Fin W → ℝ
  t : Fin N ⊕ Fin W → Fin N → ℝ
  β : Fin N ⊕ Fin W → Fin N → ℝ
  β_nonneg : ∀ i n, 0 ≤ β i n
  β_le_one : ∀ i n, β i n ≤ 1

namespace System

variable {N W : ℕ}

/-- The salvage value `v_i` of a location: `v_n` for a retailer, `v_w` for a warehouse. -/
def salvage (sys : System N W) : Fin N ⊕ Fin W → ℝ := Sum.elim sys.v sys.vw

/-- The per-unit excess profit `r_n - v_i - t_{i,n}` of shipping from location `i` to
retailer `n` (the coefficient in Eqs. (1) and (6a)). -/
def margin (sys : System N W) (i : Fin N ⊕ Fin W) (n : Fin N) : ℝ :=
  sys.r n - sys.salvage i - sys.t i n

end System

/-- The inventory position `Z⃗_n = (X_n, Y_{1,n}, …, Y_{W,n})` of one retailer (§4.1.3, p. 357):
local stock `X` and the claims `Y w` on the stock at each warehouse `w`. -/
structure Position (W : ℕ) where
  X : ℝ
  Y : Fin W → ℝ

/-- A position is nonnegative when the local stock and every claim are nonnegative. -/
def Position.Nonneg {W : ℕ} (z : Position W) : Prop :=
  0 ≤ z.X ∧ ∀ w, 0 ≤ z.Y w

/-- A profile of positions `[Z] = (Z⃗_1, …, Z⃗_N)`. All warehouse stock is claimed: the stock at
warehouse `w` is `Y_w = ∑_n Y_{w,n}`. -/
abbrev Profile (N W : ℕ) := Fin N → Position W

/-- Every retailer's position is nonnegative. -/
def Profile.Nonneg {N W : ℕ} (Z : Profile N W) : Prop :=
  ∀ n, (Z n).Nonneg

/-- A demand realization `D⃗ = (D_1, …, D_N)`. -/
abbrev Demand (N : ℕ) := Fin N → ℝ

/-- Sales from local inventory `S_n = min{X_n, D_n}`. -/
def sales {N W : ℕ} (Z : Profile N W) (D : Demand N) (n : Fin N) : ℝ :=
  min (Z n).X (D n)

/-- Residual (local) inventory `H_n = max{X_n - D_n, 0}`. -/
def residualInv {N W : ℕ} (Z : Profile N W) (D : Demand N) (n : Fin N) : ℝ :=
  max ((Z n).X - D n) 0

/-- Residual demand `E_n = max{D_n - X_n, 0}`. -/
def residualDem {N W : ℕ} (Z : Profile N W) (D : Demand N) (n : Fin N) : ℝ :=
  max (D n - (Z n).X) 0

/-- A shipping pattern `Q⃗ = {q_{i,n}}`: units shipped from location `i` to retailer `n`. -/
abbrev ShippingPlan (N W : ℕ) := Fin N ⊕ Fin W → Fin N → ℝ

/-- Location `i` belongs to `𝒮 ∪ 𝒲`: a retailer in `𝒮`, or any warehouse. -/
def LocIn {N W : ℕ} (S : Finset (Fin N)) : Fin N ⊕ Fin W → Prop
  | Sum.inl j => j ∈ S
  | Sum.inr _ => True

/-- Feasibility of a shipping pattern for coalition `𝒮` in the shipping LP (6), pp. 357–358:
* (6e) `q_{i,n} ≥ 0`, and shipments exist only on arcs `i ∈ 𝒮 ∪ 𝒲`, `n ∈ 𝒮`;
* an arc with `β_{i,n} = 0` carries nothing (those customers balk);
* (6b) `∑_{n∈𝒮} q_{i,n} ≤ H_i` for every retailer `i ∈ 𝒮`;
* (6c) `∑_{n∈𝒮} q_{w,n} ≤ ∑_{n∈𝒮} Y_{w,n}` for every warehouse `w`;
* (6d) `∑_{i∈𝒮∪𝒲} q_{i,n}/β_{i,n} ≤ E_n` for every retailer `n ∈ 𝒮`. -/
def IsFeasibleShipping {N W : ℕ} (sys : System N W) (S : Finset (Fin N)) (Z : Profile N W)
    (D : Demand N) (q : ShippingPlan N W) : Prop :=
  (∀ i n, 0 ≤ q i n) ∧
  (∀ i n, ¬ (LocIn S i ∧ n ∈ S) → q i n = 0) ∧
  (∀ i n, sys.β i n = 0 → q i n = 0) ∧
  (∀ j ∈ S, ∑ n ∈ S, q (Sum.inl j) n ≤ residualInv Z D j) ∧
  (∀ w, ∑ n ∈ S, q (Sum.inr w) n ≤ ∑ n ∈ S, (Z n).Y w) ∧
  (∀ n ∈ S, (∑ j ∈ S, q (Sum.inl j) n / sys.β (Sum.inl j) n)
      + (∑ w, q (Sum.inr w) n / sys.β (Sum.inr w) n) ≤ residualDem Z D n)

/-- The objective (6a) of coalition `𝒮`: `∑_{i∈𝒮∪𝒲, n∈𝒮} (r_n - v_i - t_{i,n}) q_{i,n}`. -/
def shippingProfit {N W : ℕ} (sys : System N W) (S : Finset (Fin N)) (q : ShippingPlan N W) : ℝ :=
  (∑ j ∈ S, ∑ n ∈ S, sys.margin (Sum.inl j) n * q (Sum.inl j) n)
    + ∑ w, ∑ n ∈ S, sys.margin (Sum.inr w) n * q (Sum.inr w) n

/-- The value `W*_𝒮([Z], D⃗)` of the snapshot allocation game SAG([Z], D⃗): the maximal excess
profit of coalition `𝒮` in the shipping LP (6), taken as the supremum of the objective (6a) over
the feasible patterns. For a nonnegative profile the feasible set contains `q = 0` and is
bounded, so the supremum is attained. -/
noncomputable def coalitionValue {N W : ℕ} (sys : System N W) (S : Finset (Fin N))
    (Z : Profile N W) (D : Demand N) : ℝ :=
  sSup (shippingProfit sys S '' {q | IsFeasibleShipping sys S Z D q})

end DecentralizedDistribution.FirstBest
