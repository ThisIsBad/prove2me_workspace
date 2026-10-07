import Mathlib

namespace KingmanSubadditive.Ergodic

open MeasureTheory

/-- The valid index pairs `s < t` of §1.1 (pp. 883–884). Values outside this
type play no role in the process. -/
abbrev Interval := {p : ℕ × ℕ // p.1 < p.2}

/-- The full two-parameter sample path, indexed only by valid pairs. -/
def path {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) : Interval → ℝ :=
  fun p => x p.1.1 p.1.2 ω

/-- The shift `x'_{st} = x_{s+1,t+1}` of (1.2.3), p. 885, on path space. -/
def shift (φ : Interval → ℝ) : Interval → ℝ :=
  fun p => φ ⟨(p.1.1 + 1, p.1.2 + 1), by omega⟩

/-- The shift of a two-parameter sample path. -/
def shiftedPath {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) : Interval → ℝ :=
  shift (path x ω)

/-- `g_t = E(x_{0t})`, (1.1.2), p. 883. The integrability condition is
carried by `S3` wherever this quantity is used in a theorem. -/
noncomputable def mean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) (t : ℕ) : ℝ := ∫ ω, x 0 t ω ∂P

/-- Condition S₁, (1.1.1), p. 883. We use the pointwise version of the
displayed inequality for every valid triple. -/
def S1 {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ (s t u : ℕ) (ω : Ω), s < t → t < u → x s u ω ≤ x s t ω + x t u ω

/-- Condition S₂, p. 884: equality of the laws of the *whole paths* before
and after shifting both indices by one. This is stronger than S₂′, which
requires equality only for individual coordinates. -/
def S2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  Measure.map (shiftedPath x) P = Measure.map (path x) P

/-- Condition S₃, (1.1.2)–(1.1.3), p. 883: each positive-time mean is finite
and the means have a common linear lower bound. -/
def S3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ t : ℕ, 1 ≤ t → Integrable (x 0 t) P) ∧
  ∃ A : ℝ, ∀ t : ℕ, 1 ≤ t → -A * (t : ℝ) ≤ mean P x t

/-- Kingman's subadditive process (§1.1, pp. 883–884): measurable random
variables on valid index pairs satisfying S₁, joint-law stationarity S₂,
and S₃. -/
def IsSubadditiveProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ s t : ℕ, s < t → Measurable (x s t)) ∧ S1 x ∧ S2 P x ∧ S3 P x

/-- An additive process, (1.1.6), p. 884: equality in S₁ along with the
same measurability, S₂ and S₃ requirements. -/
def IsAdditiveProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ s t : ℕ, s < t → Measurable (x s t)) ∧
  (∀ (s t u : ℕ) (ω : Ω), s < t → t < u →
    x s u ω = x s t ω + x t u ω) ∧ S2 P x ∧ S3 P x

/-- The finite constant `γ(x) = inf_{t≥1} g_t/t`, (1.1.5), p. 883.
Theorems using it assume S₃, which bounds the infimum below. -/
noncomputable def gamma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : ℝ :=
  ⨅ t : {t : ℕ // 1 ≤ t}, mean P x t / (t : ℝ)

/-- The invariant σ-field `𝓘` of (1.2.3)–(1.2.4), p. 885: the pullback
under the full path map of the shift-invariant measurable sets of path space.
For a measurable process this is a sub-σ-field of the ambient one. -/
noncomputable def invariantSigma {Ω : Type*} [MeasurableSpace Ω]
    (x : ℕ → ℕ → Ω → ℝ) : MeasurableSpace Ω :=
  (MeasurableSpace.invariants shift).comap (path x)

end KingmanSubadditive.Ergodic
