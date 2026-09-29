import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- The space `L∞` of payoffs, as the subtype of real functions with `MemLp X ∞ P`. -/
abbrev LInf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Type _ :=
  {X : Ω → ℝ // MemLp X ⊤ P}

/-- The family `Q ↦ -E_Q(X | G) - α(Q)`, `Q ∈ P_G`, of extended random variables appearing in
the robust representation (3), p. 5.  `E_Q(X | G)` is Mathlib's conditional expectation
`Q[X | m]` (a `G`-measurable function); the penalty `α(Q)` takes values in `[0, +∞]`, and a
finite number minus `+∞` is `-∞` in `EReal`. -/
noncomputable def reprFamily {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (α : PG m P → Ω → ENNReal) (X : Ω → ℝ) :
    PG m P → Ω → EReal :=
  fun Q ω => ((-(Q.1[X | m]) ω : ℝ) : EReal) - (α Q ω : EReal)

/-- Definition 3.1, p. 5: `α : P_G → L⁰_G([0, +∞])` is a (random) penalty function for `ρ`:
each `α(Q)` is `G`-measurable and `[0, +∞]`-valued, and for every `X ∈ L∞`
`ρ(X) = ess.sup_{Q ∈ P_G} {-E_Q(X | G) - α(Q)}` `P`-a.s. -/
def IsPenaltyFor {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (ρ : (Ω → ℝ) → Ω → ℝ) (α : PG m P → Ω → ENNReal) : Prop :=
  (∀ Q, Measurable[m] (α Q)) ∧
    ∀ X : Ω → ℝ, MemLp X ⊤ P → IsEssSup P (reprFamily m P α X) (fun ω => (ρ X ω : EReal))

/-- Definition 3.1, p. 5: `ρ` is representable, i.e. it admits a (random) penalty function. -/
def IsRepresentable {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∃ α : PG m P → Ω → ENNReal, IsPenaltyFor m P ρ α

/-- The family `B_Q = {-E_Q(X | G) - ρ(X) | X ∈ L∞}` (p. 7), indexed by `X ∈ L∞`. -/
noncomputable def penaltyFamily {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (Q : PG m P) : LInf P → Ω → EReal :=
  fun X ω => ((-(Q.1[X.1 | m]) ω - ρ X.1 ω : ℝ) : EReal)

/-- Theorem 3.2 (c), p. 6: `α*` is the minimal penalty of `ρ`,
`α*(Q) = ess.sup_{X ∈ L∞} {-E_Q(X | G) - ρ(X)}` for every `Q ∈ P_G`.  This is a predicate on a
candidate `α*`; by Theorem A.1 an essential supremum exists and is `P`-a.s. unique. -/
def IsMinimalPenalty {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ρ : (Ω → ℝ) → Ω → ℝ) (α : PG m P → Ω → ENNReal) : Prop :=
  ∀ Q : PG m P, IsEssSup P (penaltyFamily m P ρ Q) (fun ω => (α Q ω : EReal))

/-- Theorem 3.2 (a), p. 6: `ρ` is continuous from above: whenever `X_n, X ∈ L∞` and
`X_n ↘ X` `P`-a.s. (a.s. non-increasing and a.s. convergent to `X`), then `ρ(X_n) ↗ ρ(X)`
`P`-a.s. (a.s. non-decreasing and a.s. convergent to `ρ(X)`). -/
def IsContinuousFromAbove {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ (X : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ n, MemLp (X n) ⊤ P) → MemLp Y ⊤ P →
    (∀ᵐ ω ∂P, Antitone (fun n => X n ω) ∧ Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) →
    ∀ᵐ ω ∂P, Monotone (fun n => ρ (X n) ω) ∧ Tendsto (fun n => ρ (X n) ω) atTop (𝓝 (ρ Y ω))

end CondConvexRisk.Representation
