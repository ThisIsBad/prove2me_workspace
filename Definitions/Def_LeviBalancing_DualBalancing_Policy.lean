import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model

noncomputable section

namespace LeviBalancing.DualBalancing

open MeasureTheory
open scoped ENNReal

/-- The demand process of §2 (p. 288) on a probability space `(Ω, μ)` with a filtration `ℱ`
indexed by periods: `ℱ s` is the information available at the beginning of period `s`.
For `t = 1, …, T`, the demand `D t` is nonnegative and known one period later
(`ℱ (t+1)`-measurable, since `f_{t+1}` contains `d_t`). No independence, stationarity or Markov
assumption is made, and no unconditional integrability: the paper only asks that the conditional
expectations `E[D_t | f_s]` be finite, and every statement that needs integrability carries it
itself (the costs of a dual-balancing policy in `IsDualBalancing`, the demands in the existence
theorem). -/
structure DemandProcess {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℤ m)
    (μ : Measure Ω) (T : ℕ) where
  D : ℤ → Ω → ℝ
  nonneg : ∀ t : ℤ, 1 ≤ t → t ≤ (T : ℤ) → ∀ ω, 0 ≤ D t ω
  measurable : ∀ t : ℤ, 1 ≤ t → t ≤ (T : ℤ) → Measurable[ℱ (t + 1)] (D t)

/-- A feasible (nonanticipatory) policy (p. 289), given as its order process `Q`: for each period
`t = 1, …, T` the order `Q t` is nonnegative and is a function of the information `ℱ t`
available at the beginning of period `t`. -/
structure IsFeasiblePolicy {Ω : Type*} [m : MeasurableSpace Ω] (I : Instance)
    (ℱ : Filtration ℤ m) (Q : ℤ → Ω → ℝ) : Prop where
  nonneg : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → ∀ ω, 0 ≤ Q t ω
  adapted : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → Measurable[ℱ t] (Q t)

/-- The random marginal holding cost `H_t^P` (Eq. (1)) of the order process `Q`. -/
def randHolding {Ω : Type*} (I : Instance) (D Q : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => marginalHolding I (fun j => D j ω) (fun j => Q j ω) t

/-- The random marginal backlogging cost `Π_t^P` (Eq. (2)) of the order process `Q`. -/
def randBacklog {Ω : Type*} (I : Instance) (D Q : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => marginalBacklog I (fun j => D j ω) (fun j => Q j ω) t

/-- The random inventory position after ordering, `Y_t^P`. -/
def randPositionAfter {Ω : Type*} (I : Instance) (D Q : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => invPositionAfter I (fun j => D j ω) (fun j => Q j ω) t

/-- The expected cost `E[𝒞(P)]` of Eq. (4), as a lower Lebesgue integral in `[0, ∞]` of the
(nonnegative) realized cost; an infinite expected cost is `∞`, never `0`. -/
def expectedCost {Ω : Type*} [MeasurableSpace Ω] (I : Instance) (μ : Measure Ω)
    (D Q : ℤ → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (marginalCost I (fun j => D j ω) (fun j => Q j ω)) ∂μ

/-- The dual-balancing policy of §4.1 (pp. 292–293), as a property of an order process `B`:
`B` is feasible; it orders nothing in periods `T − L + 1, …, T`; and in each period
`t = 1, …, T − L` its marginal holding and backlogging costs are integrable and balanced in
conditional expectation given the information at the beginning of period `t`,
`E[H_t^B | ℱ t] = E[Π_t^B | ℱ t]` almost surely (the form used on p. 294). -/
structure IsDualBalancing {Ω : Type*} [m : MeasurableSpace Ω] (I : Instance)
    (ℱ : Filtration ℤ m) (μ : Measure Ω) (D B : ℤ → Ω → ℝ) : Prop where
  feasible : IsFeasiblePolicy I ℱ B
  zero_after : ∀ t : ℤ, (I.T : ℤ) - I.L < t → t ≤ (I.T : ℤ) → ∀ ω, B t ω = 0
  integrable_holding : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) - I.L →
    Integrable (randHolding I D B t) μ
  integrable_backlog : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) - I.L →
    Integrable (randBacklog I D B t) μ
  balance : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) - I.L →
    μ[randHolding I D B t | ℱ t] =ᵐ[μ] μ[randBacklog I D B t | ℱ t]

end LeviBalancing.DualBalancing

end
