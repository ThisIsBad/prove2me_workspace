import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- A **lifetime law**: a probability measure on `ℝ` that puts no mass on `(-∞, 0)`. The
interarrival-time distribution `A` and the service-time distribution `B` of the G/G/1 queue are
lifetime laws (p.284). -/
def IsLifetimeLaw (A : Measure ℝ) : Prop :=
  IsProbabilityMeasure A ∧ A (Set.Iio 0) = 0

/-- The cumulative distribution function `F(t) = ν((-∞, t])` of a measure `ν` on `ℝ`. For the
stationary delay law `ν` this is the book's `W_q(t)`; for `B` it is `B(t)`. -/
noncomputable def cdfOf (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ν.real (Set.Iic t)

/-- The mean `∫ x dA(x)` of a law on `ℝ` (a Bochner integral: `0` when the identity is not
integrable, so every theorem using it assumes integrability). `E[T] = meanOf A`, `E[S] = meanOf B`. -/
noncomputable def meanOf (A : Measure ℝ) : ℝ :=
  ∫ x, x ∂A

/-- The traffic intensity `ρ = λ/μ = E[S]/E[T]` of the G/G/1 queue, with `λ = 1/E[T]` and
`μ = 1/E[S]`, for interarrival law `A` and service law `B`. -/
noncomputable def trafficIntensity (A B : Measure ℝ) : ℝ :=
  meanOf B / meanOf A

/-- The law `U` of `U = S − T` for independent `S ~ B` and `T ~ A`, i.e. the convolution of `S`
and `−T` (Eq. (6.9), p.285). Independence is encoded by the product measure `B ⊗ A`. -/
noncomputable def diffLaw (A B : Measure ℝ) : Measure ℝ :=
  (B.prod A).map (fun p : ℝ × ℝ => p.1 - p.2)

/-- One step of Lindley's recursion `W_q^{(n+1)} = max(0, W_q^{(n)} + S^{(n)} − T^{(n)})` (p.284)
on laws: the law of `max(0, W + U)` when `W ~ ν` is independent of `U ~ Ulaw`. -/
noncomputable def lindleyStep (Ulaw ν : Measure ℝ) : Measure ℝ :=
  (ν.prod Ulaw).map (fun p : ℝ × ℝ => max 0 (p.1 + p.2))

/-- `ν` is a **stationary delay distribution** of the G/G/1 queue with interarrival law `A` and
service law `B`: a probability measure that Lindley's recursion maps to itself, i.e. if
`W_q^{(n)} ~ ν` is independent of `S^{(n)} ~ B` and `T^{(n)} ~ A` (themselves independent), then
`W_q^{(n+1)} ~ ν`. -/
def IsStationaryDelay (A B ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ lindleyStep (diffLaw A B) ν = ν

/-- The two-sided Laplace transform `f̄(s) = ∫_{−∞}^{∞} e^{−st} f(t) dt` of a real function
(Lebesgue measure; `0` where the integrand is not integrable). -/
noncomputable def twoSidedLaplace (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * (f t : ℂ)

/-- The function `W_q^−(t)` of Eq. (6.10) (p.285), built from a function `W` (the book's `W_q`)
and the law `U`: `W_q^−(t) = ∫_{−∞}^{t} W(t − x) dU(x)` for `t < 0` and `0` for `t ≥ 0`. The
Stieltjes integral over `(−∞, t]` is the Lebesgue integral over `Set.Iic t` against `U`. -/
noncomputable def negPart (Ulaw : Measure ℝ) (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then ∫ x in Set.Iic t, W (t - x) ∂Ulaw else 0

end QueueingFundamentals.GG1
