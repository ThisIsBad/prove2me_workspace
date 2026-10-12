import Mathlib

/-- The finite-state stochastic shortest path model of Bertsekas, "Dynamic
Programming and Optimal Control", Vol. I, 3rd ed., Section 7.2: states
`1, …, n` (here `Fin n`) plus an implicit cost-free absorbing termination
state `t`.  Applying control `u ∈ U i` at state `i` incurs cost `g i u`,
moves to state `j` with probability `p i u j`, and moves to the termination
state with the remaining probability `1 - ∑ⱼ p i u j`. -/
structure BertsekasSSPModel (n : ℕ) (C : Type) [Fintype C] where
  U : Fin n → Finset C
  hU : ∀ i, (U i).Nonempty
  p : Fin n → C → Fin n → ℝ
  g : Fin n → C → ℝ
  hp_nonneg : ∀ i u j, 0 ≤ p i u j
  hp_sum : ∀ i, ∀ u ∈ U i, ∑ j, p i u j ≤ 1

/-- An admissible (nonstationary, state-feedback) policy for the stochastic
shortest path model: a sequence of stage policies, each respecting the control
constraint sets. -/
def BertsekasSSPAdmissible {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (π : ℕ → Fin n → C) : Prop :=
  ∀ k i, π k i ∈ M.U i

/-- The DP operator `T_μ` associated with a stationary policy `μ` for the
stochastic shortest path model:
`(T_μ J)(i) = g(i, μ(i)) + ∑ⱼ p_{ij}(μ(i)) J(j)`. -/
def BertsekasSSPPolicyOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (μ : Fin n → C) (J : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => M.g i (μ i) + ∑ j, M.p i (μ i) j * J j

/-- The Bellman (value iteration) operator `T` of the stochastic shortest path
model: `(T J)(i) = min_{u ∈ U(i)} [g(i, u) + ∑ⱼ p_{ij}(u) J(j)]`
(Eq. (7.6)/(7.7)). -/
noncomputable def BertsekasSSPBellmanOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (J : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (M.U i).inf' (M.hU i) fun u => M.g i u + ∑ j, M.p i u j * J j

/-- The `N`-stage expected cost of a (possibly nonstationary) policy `π` for
the stochastic shortest path model, with zero terminal cost:
`BertsekasSSPNCost M π N i = E[∑_{k<N} g(x_k, μ_k(x_k)) | x₀ = i]`.
The infinite-horizon cost of `π` is the limit as `N → ∞`. -/
def BertsekasSSPNCost {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) : (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => 0
  | π, N + 1 =>
      BertsekasSSPPolicyOp M (π 0)
        (BertsekasSSPNCost M (fun k => π (k + 1)) N)

/-- `BertsekasSSPSurvival M π m i` is the probability that the termination
state has not been reached after `m` stages, starting from state `i` and using
policy `π` — the quantity `P{x_m ≠ t | x₀ = i, π}` of Assumption 7.2.1. -/
def BertsekasSSPSurvival {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) : (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => fun _ => 1
  | π, m + 1 => fun i =>
      ∑ j, M.p i (π 0 i) j *
        BertsekasSSPSurvival M (fun k => π (k + 1)) m j

open Classical in
/-- `BertsekasSSPAvoidProb M s π m i` is the probability that the designated
state `s` is not visited during the first `m` stages (i.e. by any of
`x₁, …, x_m`), starting from `x₀ = i` under policy `π`.  Assumption 7.4.1 of
Section 7.4 requires this to be `< 1` for some `m`, uniformly over policies
and initial states. -/
noncomputable def BertsekasSSPAvoidProb {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (s : Fin n) :
    (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => fun _ => 1
  | π, m + 1 => fun i =>
      ∑ j, if j = s then 0 else
        M.p i (π 0 i) j *
          BertsekasSSPAvoidProb M s (fun k => π (k + 1)) m j

/-- The DP operator `T_μ` of the α-discounted finite-state problem of
Section 7.3: `(T_μ J)(i) = g(i, μ(i)) + α ∑ⱼ p_{ij}(μ(i)) J(j)`. -/
def BertsekasDiscountedPolicyOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (α : ℝ) (μ : Fin n → C) (J : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => M.g i (μ i) + α * ∑ j, M.p i (μ i) j * J j

/-- The Bellman operator of the α-discounted finite-state problem of
Section 7.3 (Eq. (7.21)/(7.22)):
`(T J)(i) = min_{u ∈ U(i)} [g(i, u) + α ∑ⱼ p_{ij}(u) J(j)]`. -/
noncomputable def BertsekasDiscountedBellmanOp {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (α : ℝ) (J : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (M.U i).inf' (M.hU i) fun u =>
    M.g i u + α * ∑ j, M.p i u j * J j

/-- The `N`-stage expected α-discounted cost of a (possibly nonstationary)
policy `π`: `BertsekasDiscountedNCost M α π N i =
E[∑_{k<N} α^k g(x_k, μ_k(x_k)) | x₀ = i]`. -/
def BertsekasDiscountedNCost {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (α : ℝ) : (ℕ → Fin n → C) → ℕ → Fin n → ℝ
  | _, 0 => 0
  | π, N + 1 =>
      BertsekasDiscountedPolicyOp M α (π 0)
        (BertsekasDiscountedNCost M α (fun k => π (k + 1)) N)