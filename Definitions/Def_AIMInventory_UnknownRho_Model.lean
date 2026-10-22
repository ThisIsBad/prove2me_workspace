import Mathlib
import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace AIMInventory.UnknownRho

/-- Parameters of the non-perishable AIM rule (3)--(5), including the arbitrary
initial target in the known interval. -/
structure Parameters where
  h : ℝ
  b : ℝ
  barY : ℝ
  gamma : ℝ
  initial : ℝ
  h_pos : 0 < h
  b_pos : 0 < b
  barY_pos : 0 < barY
  gamma_pos : 0 < gamma
  initial_nonneg : 0 ≤ initial
  initial_le : initial ≤ barY

abbrev DemandPath := CappedBaseStock.DemandPath
abbrev DemandLaw := CappedBaseStock.DemandLaw

/-- Equation (1) at a real stock level; only nonnegative levels occur in AIM. -/
def Q (P : DemandLaw) (c : Parameters) (y : ℝ) : ℝ :=
  LostSalesOrderUpTo.Asymptotic.backorderCost P.law c.h c.b (Real.toNNReal y)

/-- Equation (4), for the paper's positive period numbers. -/
def stepSize (c : Parameters) (t : ℕ) : ℝ :=
  c.gamma * c.barY / (max c.b c.h * Real.sqrt (t : ℝ))

/-- Equation (5): the sign is determined by the target, not the implemented level. -/
def observedSlope (c : Parameters) (target : ℝ) (demand : ℝ≥0) : ℝ :=
  if (demand : ℝ) < target then c.h else -c.b

/-- State at period `n+1` is (target, implemented level, on-hand stock).
The demand `d n` is the paper's `D_(n+1)`. -/
def aimState (c : Parameters) (d : DemandPath) : ℕ → ℝ × ℝ × ℝ
  | 0 => (c.initial, c.initial, 0)
  | n + 1 =>
      let prior := aimState c d n
      let nextTarget := max (min (prior.1 - stepSize c (n + 1) *
        observedSlope c prior.1 (d n)) c.barY) 0
      let nextHand := max (prior.2.1 - (d n : ℝ)) 0
      (nextTarget, max nextTarget nextHand, nextHand)

/-- The paper's target `ŷ_t`, indexed from 1. -/
def aimTarget (c : Parameters) (d : DemandPath) (t : ℕ) : ℝ :=
  (aimState c d (t - 1)).1

/-- The paper's implemented order-up-to level `y_t`, indexed from 1. -/
def aimLevel (c : Parameters) (d : DemandPath) (t : ℕ) : ℝ :=
  (aimState c d (t - 1)).2.1

/-- The paper's on-hand inventory `x_t`, indexed from 1. -/
def onHand (c : Parameters) (d : DemandPath) (t : ℕ) : ℝ :=
  (aimState c d (t - 1)).2.2

/-- Equation (8), `Λ₂(T)`: the expectation of average signed cost difference. -/
def lambdaTwo (P : DemandLaw) (c : Parameters) (T : ℕ) : ℝ :=
  ∫ d, ((T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
    (Q P c (aimLevel c d t) - Q P c (aimTarget c d t)))
    ∂CappedBaseStock.demandPathLaw P

/-- The scale `m = h γ ȳ / max{b,h}` in Theorem 8. -/
def m (c : Parameters) : ℝ := c.h * c.gamma * c.barY / max c.b c.h

/-- Lindley's fixed-inflow waiting time: `W₁=0`, then
`W_(t+1)=[W_t+θ-D_t]⁺` for `t≥1`. -/
def W (d : DemandPath) (θ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => if t = 0 then 0 else max (W d θ t + θ - (d (t - 1) : ℝ)) 0

/-- Decreasing-inflow waiting time: `Z₁=0`, then
`Z_(t+1)=[Z_t+θ/√t-D_t]⁺` for `t≥1`. -/
def Z (d : DemandPath) (θ : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => if t = 0 then 0 else
      max (Z d θ t + θ / Real.sqrt (t : ℝ) - (d (t - 1) : ℝ)) 0

/-- Equation (12): first nonpositive partial sum, including time zero. The
infimum is `∞` if no time satisfies the condition. -/
def K (d : DemandPath) (θ z : ℝ) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ n : ℕ, u = (n : ℝ≥0∞) ∧
    z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) ≤ 0}

/-- `|J₁(θ)| = τ₁-1`: first positive period count returning `W` to zero.
It is `∞` on a path with no return. -/
def firstBusyLength (d : DemandPath) (θ : ℝ) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ n : ℕ, 1 ≤ n ∧ u = (n : ℝ≥0∞) ∧ W d θ (n + 1) = 0}

/-- The paper's positive-integer threshold `T̃=⌈(m/ρ′)²⌉` in the theorem's
regime `0<ρ′<m`. The max makes the auxiliary definition total elsewhere. -/
def threshold (c : Parameters) (ρ' : ℝ) : ℕ :=
  max 1 (Nat.ceil ((m c / ρ') ^ 2))

/-- `K̃`: first return of `Z(m)` strictly after `T̃`; infinite on a
path with no such return. -/
def restartTime (c : Parameters) (ρ' : ℝ) (d : DemandPath) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ t : ℕ,
    (threshold c ρ' < t) ∧ u = (t : ℝ≥0∞) ∧ Z d (m c) t = 0}

/-- The first-stop bound's initial height, `2√2 m²/ρ′`. -/
def initialHeight (c : Parameters) (ρ' : ℝ) : ℝ :=
  2 * Real.sqrt 2 * (m c) ^ 2 / ρ'

/-- Expected squared length of the first fixed-inflow busy period. -/
def busySecondMoment (P : DemandLaw) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, (firstBusyLength d θ) ^ 2 ∂CappedBaseStock.demandPathLaw P

/-- The expected hitting time appearing in Theorem 8. -/
def expectedK (P : DemandLaw) (θ z : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, K d θ z ∂CappedBaseStock.demandPathLaw P

/-- The fourth central demand moment in Lemma 9. -/
def centralFourth (P : DemandLaw) : ℝ :=
  ∫ d : ℝ≥0, ((d : ℝ) - CappedBaseStock.mean P) ^ 4 ∂P.law

end AIMInventory.UnknownRho
