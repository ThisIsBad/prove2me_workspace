import Mathlib

namespace FragLOB.Collapse

open MeasureTheory

/-- The parameters of the fragmented limit order book of §2 (pp. 1328–1330):
`N` exchanges indexed by `Fin N`; dedicated limit-order rates `lam i` (λ_i), the optimized
limit-order rate `Lam` (Λ), the aggregate market-order rate `mu` (μ), the attraction
coefficients `beta i` (β_i) of (5), and the effective rebates `r` (r̃_0, …, r̃_N).
Routing options are indexed by `Fin (N+1)`: option `0` is the market order, option `i.succ`
is exchange `i`. -/
structure Market (N : ℕ) where
  lam : Fin N → ℝ
  Lam : ℝ
  mu : ℝ
  beta : Fin N → ℝ
  r : Fin (N + 1) → ℝ

/-- Standing assumptions on the rates (pp. 1328–1330): λ_i ≥ 0, Λ > 0, μ > 0, β_i > 0.
The rebates are unconstrained. -/
def Market.Standing {N : ℕ} (M : Market N) : Prop :=
  (∀ i, 0 ≤ M.lam i) ∧ 0 < M.Lam ∧ 0 < M.mu ∧ ∀ i, 0 < M.beta i

/-- A feasible routing decision for one type, constraint (9): a point of the simplex over the
`N + 1` options. -/
def IsSimplexPoint {N : ℕ} (p : Fin (N + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The set 𝒫 of routing decisions (p. 1331): every `γ ↦ π_i(γ)` is measurable and `π(γ)`
satisfies (9) for every type `γ ≥ 0`. Values at `γ < 0` are unconstrained. -/
def IsRouting {N : ℕ} (pi : ℝ → Fin (N + 1) → ℝ) : Prop :=
  (∀ i, Measurable fun γ => pi γ i) ∧ ∀ γ, 0 ≤ γ → IsSimplexPoint (pi γ)

/-- The workload `W = Σ_i β_i Q_i` (§3.2, p. 1331). -/
def workload {N : ℕ} (M : Market N) (Q : Fin N → ℝ) : ℝ :=
  ∑ j, M.beta j * Q j

/-- The market-order rate of exchange `i`, (4) with the linear attraction (5):
`μ_i(Q) = μ β_i Q_i / Σ_j β_j Q_j`. -/
noncomputable def marketRate {N : ℕ} (M : Market N) (Q : Fin N → ℝ) (i : Fin N) : ℝ :=
  M.mu * M.beta i * Q i / workload M Q

/-- The expected delay at exchange `i`: `ED_i = Q_i / μ_i(Q)` by (1) when `Q_i > 0`, and the
value `W / (μ β_i)` of (12) at an empty exchange (where (1) reads `0/0`). -/
noncomputable def delay {N : ℕ} (M : Market N) (Q : Fin N → ℝ) (i : Fin N) : ℝ :=
  if 0 < Q i then Q i / marketRate M Q i else workload M Q / (M.mu * M.beta i)

/-- The payoff of a type-`γ` investor using the randomized routing `p` when the delays are
`d`, the objective of (10): `p_0 γ r̃_0 + Σ_i p_i (γ r̃_i − d_i)`. -/
def payoff {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) (p : Fin (N + 1) → ℝ) : ℝ :=
  p 0 * (γ * M.r 0) + ∑ i : Fin N, p i.succ * (γ * M.r i.succ - d i)

/-- `p` is an optimal solution of (10) for type `γ` under delays `d`. -/
def IsBestResponse {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ)
    (p : Fin (N + 1) → ℝ) : Prop :=
  IsSimplexPoint p ∧ ∀ q, IsSimplexPoint q → payoff M d γ q ≤ payoff M d γ p

/-- Definition 1 (Equilibrium), p. 1331, with individual rationality (i) read for `F`-almost
every type, and with a nonzero book (`β^⊤Q > 0`, without which (4) is undefined).
(ii) is the flow balance (11). -/
def IsEquilibrium {N : ℕ} (M : Market N) (F : Measure ℝ) (pi : ℝ → Fin (N + 1) → ℝ)
    (Q : Fin N → ℝ) : Prop :=
  IsRouting pi ∧ (∀ i, 0 ≤ Q i) ∧ 0 < workload M Q ∧
    (∀ᵐ γ ∂F, IsBestResponse M (delay M Q) γ (pi γ)) ∧
    ∀ i, M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F = marketRate M Q i

/-- The objective of the aggregated problem (13) at workload `W`:
`∫ {π_0(γ) γ r̃_0 + Σ_i π_i(γ)(γ r̃_i − W/(μ β_i))} dF(γ)`. -/
noncomputable def aggObjective {N : ℕ} (M : Market N) (F : Measure ℝ) (W : ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) : ℝ :=
  ∫ γ, payoff M (fun i => W / (M.mu * M.beta i)) γ (pi γ) ∂F

/-- `pi` is an optimal solution of (13) over the routing decisions 𝒫. -/
def IsAggOptimal {N : ℕ} (M : Market N) (F : Measure ℝ) (W : ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) : Prop :=
  IsRouting pi ∧ ∀ pi', IsRouting pi' → aggObjective M F W pi' ≤ aggObjective M F W pi

/-- The aggregate flow balance (14): `Σ_i (λ_i + Λ ∫ π_i dF) = μ`. -/
def AggBalance {N : ℕ} (M : Market N) (F : Measure ℝ) (pi : ℝ → Fin (N + 1) → ℝ) : Prop :=
  ∑ i, (M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F) = M.mu

/-- The lifting map (15): `Q_i = (λ_i + Λ ∫ π_i dF) W / (μ β_i)`. -/
noncomputable def lift {N : ℕ} (M : Market N) (F : Measure ℝ) (pi : ℝ → Fin (N + 1) → ℝ)
    (W : ℝ) (i : Fin N) : ℝ :=
  (M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F) * W / (M.mu * M.beta i)

end FragLOB.Collapse
