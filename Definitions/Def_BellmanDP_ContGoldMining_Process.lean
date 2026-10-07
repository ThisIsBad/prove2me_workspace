import Mathlib

namespace BellmanDP.ContGoldMining

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 7, Eq. (7.2), p. 228, and § 12, Eq. (12.1),
p. 233: the rate parameters of the continuous gold-mining process with three decisions
`A` (index `0`), `B` (index `1`), `C` (index `2`).
Decision `A` removes gold from mine A at relative rate `r₁` and stops the machine at rate `q₁`;
`B` removes gold from mine B at relative rate `r₂` and stops the machine at rate `q₂`;
`C` removes gold from A at relative rate `r₃` and from B at relative rate `r₄`, and stops the
machine at rate `q₃`. The two-choice process of § 7 is the case in which `C` is never used. -/
structure Params where
  q₁ : ℝ
  q₂ : ℝ
  q₃ : ℝ
  r₁ : ℝ
  r₂ : ℝ
  r₃ : ℝ
  r₄ : ℝ

namespace Params

/-- Failure rate of decision `i`: `(q₁, q₂, q₃)`. -/
def q (P : Params) : Fin 3 → ℝ := ![P.q₁, P.q₂, P.q₃]

/-- Rate at which decision `i` depletes mine A: `(r₁, 0, r₃)` (Eq. (12.1), first line). -/
def a (P : Params) : Fin 3 → ℝ := ![P.r₁, 0, P.r₃]

/-- Rate at which decision `i` depletes mine B: `(0, r₂, r₄)` (Eq. (12.1), second line). -/
def b (P : Params) : Fin 3 → ℝ := ![0, P.r₂, P.r₄]

/-- All rates of the three-choice process are positive (the chapter's implicit range for rates). -/
def Positive (P : Params) : Prop :=
  0 < P.q₁ ∧ 0 < P.q₂ ∧ 0 < P.q₃ ∧ 0 < P.r₁ ∧ 0 < P.r₂ ∧ 0 < P.r₃ ∧ 0 < P.r₄

/-- The two-choice process of § 7 with data `(q₁, q₂, r₁, r₂)`; the entries `q₃, r₃, r₄` are set
to `0` and are never used, because the two-choice control gives `C` weight `0`. -/
def two (q₁ q₂ r₁ r₂ : ℝ) : Params := ⟨q₁, q₂, 0, r₁, r₂, 0, 0⟩

end Params

/-- A control of the three-choice process: `φ i t` is the proportion `φ_{i+1}(t)` of time devoted
to decision `i` at time `t` (Eq. (12.1)). -/
abbrev Control := Fin 3 → ℝ → ℝ

/-- Eq. (12.2), p. 233: an admissible control is measurable with `φ_i(t) ≥ 0` and
`φ₁(t) + φ₂(t) + φ₃(t) = 1` for all `t`. -/
def Admissible (φ : Control) : Prop :=
  (∀ i, Measurable (φ i)) ∧ (∀ i t, 0 ≤ φ i t) ∧ ∀ t, ∑ i, φ i t = 1

/-- The two-choice control of § 7 determined by `φ₁`: `φ₂ = 1 − φ₁` and `φ₃ = 0`
(Eq. (7.3)). -/
def twoChoice (φ₁ : ℝ → ℝ) : Control := fun i t => ![φ₁ t, 1 - φ₁ t, 0] i

/-- Eq. (7.3), p. 228: an admissible two-choice control is a measurable `φ₁` with
`0 ≤ φ₁(t) ≤ 1` for all `t`. -/
def TwoAdmissible (φ₁ : ℝ → ℝ) : Prop :=
  Measurable φ₁ ∧ ∀ t, φ₁ t ∈ Set.Icc (0 : ℝ) 1

/-- Cumulative time `Φ_i(t) = ∫₀ᵗ φ_i(s) ds` devoted to decision `i` up to time `t`. -/
noncomputable def cumTime (φ : Control) (i : Fin 3) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, φ i s

/-- Gold remaining in mine A at time `t`, `x(t) = x₀ exp(−r₁Φ₁(t) − r₃Φ₃(t))`: the solution of
`dx/dt = −[φ₁ r₁ + φ₃ r₃] x`, `x(0) = x₀` (Eqs. (7.2), (12.1)). -/
noncomputable def stateX (P : Params) (x₀ : ℝ) (φ : Control) (t : ℝ) : ℝ :=
  x₀ * Real.exp (-∑ i, P.a i * cumTime φ i t)

/-- Gold remaining in mine B at time `t`, `y(t) = y₀ exp(−r₂Φ₂(t) − r₄Φ₃(t))`: the solution of
`dy/dt = −[φ₂ r₂ + φ₃ r₄] y`, `y(0) = y₀`. -/
noncomputable def stateY (P : Params) (y₀ : ℝ) (φ : Control) (t : ℝ) : ℝ :=
  y₀ * Real.exp (-∑ i, P.b i * cumTime φ i t)

/-- Probability that the machine survives until `t`, `p(t) = exp(−q₁Φ₁(t) − q₂Φ₂(t) − q₃Φ₃(t))`:
the solution of `dp/dt = −p [φ₁ q₁ + φ₂ q₂ + φ₃ q₃]`, `p(0) = 1`. -/
noncomputable def survival (P : Params) (φ : Control) (t : ℝ) : ℝ :=
  Real.exp (-∑ i, P.q i * cumTime φ i t)

/-- The rate `f′(t) = p(t) [(φ₁ r₁ + φ₃ r₃) x(t) + (φ₂ r₂ + φ₃ r₄) y(t)]` at which expected gold
is mined (last line of Eqs. (7.2), (12.1)). -/
noncomputable def goldRate (P : Params) (x₀ y₀ : ℝ) (φ : Control) (t : ℝ) : ℝ :=
  survival P φ t *
    ∑ i, φ i t * (P.a i * stateX P x₀ φ t + P.b i * stateY P y₀ φ t)

/-- Expected amount of gold mined up to time `T`, `f(T) = ∫₀ᵀ f′(t) dt` (`f(0) = 0`). -/
noncomputable def gold (P : Params) (x₀ y₀ : ℝ) (φ : Control) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, goldRate P x₀ y₀ φ t

/-- Expected total amount of gold mined, `f(∞) = ∫₀^∞ f′(t) dt`, as an extended nonnegative real
(a lower Lebesgue integral, so it has no junk value when the integrand is not integrable). -/
noncomputable def goldInfty (P : Params) (x₀ y₀ : ℝ) (φ : Control) : ENNReal :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (goldRate P x₀ y₀ φ t)

/-- Ch. VIII, Theorem 1, Eq. (2), p. 231: the control `φ₁` follows the feedback rule
`φ₁ = 1` where `q₁ r₂ y < q₂ r₁ x`, `φ₂ = 1` (i.e. `φ₁ = 0`) where `q₁ r₂ y > q₂ r₁ x`, and
`φ₁ = r₂/(r₁ + r₂)`, `φ₂ = r₁/(r₁ + r₂)` where `q₁ r₂ y = q₂ r₁ x`, evaluated along its own
two-choice trajectory `(x(t), y(t))` from `(x₀, y₀)`, for almost every `t ≥ 0`. -/
def FollowsIndexRule (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (φ₁ : ℝ → ℝ) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
    let x := stateX (Params.two q₁ q₂ r₁ r₂) x₀ (twoChoice φ₁) t
    let y := stateY (Params.two q₁ q₂ r₁ r₂) y₀ (twoChoice φ₁) t
    (q₁ * r₂ * y < q₂ * r₁ * x → φ₁ t = 1) ∧
    (q₂ * r₁ * x < q₁ * r₂ * y → φ₁ t = 0) ∧
    (q₁ * r₂ * y = q₂ * r₁ * x → φ₁ t = r₂ / (r₁ + r₂))

end BellmanDP.ContGoldMining
