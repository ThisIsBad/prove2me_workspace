import Mathlib

noncomputable section

namespace LeviBalancing.DualBalancing

open Finset

/-- An instance of the uncapacitated periodic-review stochastic inventory control problem of
Levi, Pál, Roundy & Shmoys (2007), §2, pp. 288–290, in the transformed form of §4 (p. 292):
ordering costs `c_t = 0` and no discounting (`α = 1`).

* `T` is the number of periods `1, …, T`; `L` is the (known, integer) lead time.
* `h t` is the per-unit holding cost and `p t` the per-unit backlogging penalty of period `t`;
  both are nonnegative for `t = 1, …, T`.
* `ni0` is the net inventory at time `0` (it may be negative, i.e. backorders).
* `q j`, for `1 - L ≤ j ≤ 0`, are the last `L` orders, placed before the horizon and arriving in
  periods `1, …, L`; they are nonnegative.

Periods are integers (`ℤ`); values of `h`, `p`, `q` outside the stated ranges are never used. -/
structure Instance where
  T : ℕ
  L : ℕ
  h : ℤ → ℝ
  p : ℤ → ℝ
  ni0 : ℝ
  q : ℤ → ℝ
  h_nonneg : ∀ t : ℤ, 1 ≤ t → t ≤ (T : ℤ) → 0 ≤ h t
  p_nonneg : ∀ t : ℤ, 1 ≤ t → t ≤ (T : ℤ) → 0 ≤ p t
  q_nonneg : ∀ j : ℤ, 1 - (L : ℤ) ≤ j → j ≤ 0 → 0 ≤ q j

/-- Accumulated demand `D_[s,t] = ∑_{j=s}^{t} d_j` along a demand path `d`, with the paper's
convention `D_j := 0` for `j ≤ 0` (p. 291): only indices `j ≥ 1` are summed. -/
def cumDemand (d : ℤ → ℝ) (s t : ℤ) : ℝ :=
  ∑ j ∈ Icc (max s 1) t, d j

/-- The order placed in period `t`: the given pipeline order `q_t` for `t ≤ 0`
(`Q_t^P = q_t` for `t ≤ 0`, p. 291) and the policy's order `Q t` for `t ≥ 1`. -/
def order (I : Instance) (Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  if t ≤ 0 then I.q t else Q t

/-- Inventory position `X_t` at the beginning of period `t`, before ordering (p. 289):
`X_t = NI_{t-1} + ∑_{j=t-L}^{t-1} Q_j`, which unrolls to
`X_t = ni_0 + ∑_{j=1-L}^{t-1} Q_j − D_[1,t−1]`. -/
def invPosition (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.ni0 + ∑ j ∈ Ico (1 - (I.L : ℤ)) t, order I Q j - cumDemand d 1 (t - 1)

/-- Inventory position after ordering in period `t`: `Y_t = X_t + Q_t` (p. 289). -/
def invPositionAfter (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  invPosition I d Q t + order I Q t

/-- Net inventory `NI_t` at the end of period `t` (p. 289, events (i)–(iii)): the order placed in
period `t − L` arrives in period `t`, then demand `d_t` is served, so
`NI_t = NI_{t−1} + Q_{t−L} − D_t = ni_0 + ∑_{j=1-L}^{t-L} Q_j − D_[1,t]`. -/
def netInventory (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.ni0 + ∑ j ∈ Icc (1 - (I.L : ℤ)) (t - I.L), order I Q j - cumDemand d 1 t

/-- The (traditional) cost of period `t` (p. 289, event (iv), with `c_t = 0`): holding cost
`h_t · NI_t⁺` plus backlogging penalty `p_t · NI_t⁻`. -/
def periodCost (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.h t * max (netInventory I d Q t) 0 + I.p t * max (-netInventory I d Q t) 0

/-- Marginal holding cost, Eq. (1) with `c_t = 0` (pp. 291–292):
`H_t = ∑_{j=t+L}^{T} h_j (Q_t − (D_[t,j] − X_t)⁺)⁺`, the holding cost the `Q_t` units ordered in
period `t` incur from their arrival until the end of the horizon. -/
def marginalHolding (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑ j ∈ Icc (t + I.L) (I.T : ℤ),
    I.h j * max (order I Q t - max (cumDemand d t j - invPosition I d Q t) 0) 0

/-- Marginal backlogging cost, Eq. (2) (p. 291): the backlogging penalty incurred in period
`t + L`, `Π_t = p_{t+L} (D_[t,t+L] − (X_t + Q_t))⁺ = p_{t+L} (D_[t,t+L] − Y_t)⁺`. -/
def marginalBacklog (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.p (t + I.L) * max (cumDemand d t (t + I.L) - invPositionAfter I d Q t) 0

/-- `H_(−∞,0]` of Eq. (3) (p. 291): the total holding cost incurred over periods `1, …, T` by
units ordered before period 1, i.e. by the initial on-hand stock `ni_0⁺` and by the pipeline
orders `q_t`, `1 − L ≤ t ≤ 0` (each held from its arrival period `t + L` on, by the
first-ordered, first-consumed rule of §3.2). It depends only on the instance and the demand
path. -/
def initialHolding (I : Instance) (d : ℤ → ℝ) : ℝ :=
  ∑ j ∈ Icc (1 : ℤ) (I.T : ℤ), I.h j * max (I.ni0 - cumDemand d 1 j) 0 +
  ∑ t ∈ Icc (1 - (I.L : ℤ)) 0, ∑ j ∈ Icc (t + I.L) (I.T : ℤ),
    I.h j * max (I.q t -
      max (cumDemand d t j - (I.ni0 + ∑ i ∈ Ico (1 - (I.L : ℤ)) t, I.q i)) 0) 0

/-- The cost `𝒞(P)` of Eq. (4) (p. 292) along one realization:
`𝒞(P) = ∑_{t=1}^{T−L} (H_t + Π_t)`. -/
def marginalCost (I : Instance) (d Q : ℤ → ℝ) : ℝ :=
  ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), (marginalHolding I d Q t + marginalBacklog I d Q t)

end LeviBalancing.DualBalancing

end
