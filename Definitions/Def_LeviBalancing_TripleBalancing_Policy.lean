import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model

open MeasureTheory

noncomputable section

namespace LeviBalancing.TripleBalancing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A feasible (nonanticipatory) policy is an order process `Q`, `Q t ω` the number of units
ordered in period `t`, with `Q t ≥ 0` and `Q t` determined by the information `ℱ t` available at
the beginning of period `t` (p. 289).  The current inventory level is itself `ℱ t`-measurable, so
this is the paper's "uses only `f_s` and the current inventory level". -/
def IsFeasiblePolicy (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 ≤ Q t ω) ∧ ∀ t, Measurable[M.ℱ t] (Q t)

/-- `x_t`: the inventory level at the beginning of period `t`, before ordering
(`x_1 = x₁`, `x_{t+1} = x_t + Q_t − D_t`; lead time `L = 0`). -/
def levelBefore (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.x₁ + ∑ j ∈ Finset.Ico 1 t, (Q j ω - M.D j ω)

/-- `y_t = x_t + Q_t`: the inventory level after the order of period `t`. -/
def levelAfter (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  levelBefore M Q t ω + Q t ω

/-- Cost of period `t`: the fixed cost `K` if `Q_t > 0`, the holding cost `h_t (y_t − D_t)⁺` and the
backlogging penalty `p_t (D_t − y_t)⁺` charged on the net inventory at the end of period `t`
(p. 289 (iv), p. 299). -/
def periodCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (if 0 < Q t ω then M.K else 0)
    + M.h t * max (levelAfter M Q t ω - M.D t ω) 0
    + M.p t * max (M.D t ω - levelAfter M Q t ω) 0

/-- `𝒞(Q)`: the total cost over periods `1, …, T` (undiscounted, `α = 1`). -/
def totalCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 M.T, periodCost M Q t ω

/-- `E[𝒞(Q)]`, as the lower Lebesgue integral of the nonnegative total cost in `ℝ≥0∞`
(an infinite expected cost is `⊤`, never `0`). -/
def expectedCost (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (totalCost M Q ω) ∂M.μ

end LeviBalancing.TripleBalancing

end
