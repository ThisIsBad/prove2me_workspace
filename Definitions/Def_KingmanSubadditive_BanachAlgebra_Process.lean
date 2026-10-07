import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- The whole sample path `(x_st)_{s<t}` of a two-parameter family at the sample point `ω`. The
value type `β` is `ℝ` for the processes of §1.1 and `EReal` for the log-norm process of §2.3. -/
def path {Ω β : Type*} (x : ℕ → ℕ → Ω → β) (ω : Ω) : KingmanSubadditive.Ergodic.Interval → β :=
  fun p => x p.1.1 p.1.2 ω

/-- The shifted sample path `(x_{s+1,t+1})_{s<t}` (§1.1, p. 884, condition S₂; the shift
`x'_st = x_{s+1,t+1}` of (1.2.3), p. 885). -/
def shiftedPath {Ω β : Type*} (x : ℕ → ℕ → Ω → β) (ω : Ω) : KingmanSubadditive.Ergodic.Interval → β :=
  fun p => x (p.1.1 + 1) (p.1.2 + 1) ω

/-- Measurability: every `x_st`, `s < t`, is a random variable. -/
def IsMeasurableFamily {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (x : ℕ → ℕ → Ω → β) : Prop :=
  ∀ s t : ℕ, s < t → Measurable (x s t)

/-- Condition **S₁**, (1.1.1), p. 883: whenever `s < t < u`, `x_su ≤ x_st + x_tu`.

**Formalization Note.** The inequality between random variables is required almost surely,
separately for each triple `s < t < u` (countably many null sets). This is weaker than a pointwise
requirement, so theorems assuming it are at least as strong as with the pointwise reading. -/
def S1 {Ω β : Type*} [MeasurableSpace Ω] [Add β] [LE β] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → β) : Prop :=
  ∀ s t u : ℕ, s < t → t < u → ∀ᵐ ω ∂P, x s u ω ≤ x s t ω + x t u ω

/-- Condition **S₂**, p. 884: "The joint distributions of the process `(x_{s+1,t+1})` are the same
as those of `(x_st)`." Encoded as equality of the laws of the whole shifted and unshifted sample
paths on the product σ-algebra of `Interval → β` (all finite-dimensional distributions). This is
strictly stronger than the one-dimensional condition S₂′. -/
def S2 {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → β) : Prop :=
  Measure.map (shiftedPath x) P = Measure.map (path x) P

/-- Condition **S₃′**, p. 885, for a real process: `E(x₀₁⁺) < ∞`, written as the lower Lebesgue
integral of the positive part `x₀₁⁺ = max(x₀₁, 0)`. -/
def S3' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∫⁻ ω, ENNReal.ofReal (x 0 1 ω) ∂P < ⊤

/-- A **subadditive process** (§1.1, p. 884): a family of real random variables `x_st`, `s < t`,
satisfying S₁, S₂ and S₃. -/
def IsSubadditiveProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  IsMeasurableFamily x ∧ S1 P x ∧ S2 P x ∧ KingmanSubadditive.Ergodic.S3 P x

/-- The truncated process of the proof of Theorem 2 (p. 886):
`x_st^(N) = max(x_st, −N(t − s))`. -/
def truncate {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) (N : ℕ) : ℕ → ℕ → Ω → ℝ :=
  fun s t ω => max (x s t ω) (-(N : ℝ) * ((t : ℝ) - (s : ℝ)))

/-- The extended-real expectation `E(f) = ∫ f⁺ dP − ∫ f⁻ dP ∈ [−∞, +∞]` of an `EReal`-valued
random variable, the difference of the lower Lebesgue integrals of the positive part `f⁺` and the
negative part `f⁻ = (−f)⁺`, computed in `EReal`.

**Formalization Note.** This is the expectation the paper uses whenever a mean may be `−∞`
((1.2.9), (1.2.10), (2.3.5)). It is meaningful when `∫ f⁺ < ∞`; every theorem that uses it either
assumes or concludes that. (If both parts were `+∞`, `EReal` subtraction would return `⊥`; that
case never arises in the statements of this mission.) It is never a Bochner integral, which would
return `0` for a non-integrable function. -/
noncomputable def eMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → EReal) : EReal :=
  ((∫⁻ ω, (f ω).toENNReal ∂P : ENNReal) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂P : ENNReal) : EReal)

end KingmanSubadditive.BanachAlgebra
