import Mathlib

open MeasureTheory Filter Topology

namespace CondConvexRisk.Representation

/-- Unconditional convex risk measure on `L∞(Ω, F, P)` (Section 3, p. 5; Föllmer–Schied,
*Stochastic Finance* (2002), Definitions 4.1 and 4.4): `ρ₀ : L∞ → ℝ` is well defined on
`P`-classes, monotone, cash invariant (`ρ₀(X + c) = ρ₀(X) - c` for constants `c`) and convex
(for scalar weights `λ ∈ [0, 1]`).  `ρ₀` is unconstrained outside `L∞`. -/
structure IsConvexRiskMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ₀ : (Ω → ℝ) → ℝ) : Prop where
  ae_congr : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X =ᵐ[P] Y → ρ₀ X = ρ₀ Y
  monotone : ∀ X Y : Ω → ℝ, MemLp X ⊤ P → MemLp Y ⊤ P → X ≤ᵐ[P] Y → ρ₀ Y ≤ ρ₀ X
  cash : ∀ (X : Ω → ℝ) (c : ℝ), MemLp X ⊤ P → ρ₀ (X + fun _ => c) = ρ₀ X - c
  convex : ∀ (X Y : Ω → ℝ) (t : ℝ), MemLp X ⊤ P → MemLp Y ⊤ P → 0 ≤ t → t ≤ 1 →
    ρ₀ (t • X + (1 - t) • Y) ≤ t * ρ₀ X + (1 - t) * ρ₀ Y

/-- Continuity from above of an unconditional risk measure: `X_n, X ∈ L∞`, `X_n ↘ X` `P`-a.s.
implies `ρ₀(X_n) ↗ ρ₀(X)`. -/
def IsContinuousFromAbove₀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ₀ : (Ω → ℝ) → ℝ) : Prop :=
  ∀ (X : ℕ → Ω → ℝ) (Y : Ω → ℝ), (∀ n, MemLp (X n) ⊤ P) → MemLp Y ⊤ P →
    (∀ᵐ ω ∂P, Antitone (fun n => X n ω) ∧ Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) →
    Monotone (fun n => ρ₀ (X n)) ∧ Tendsto (fun n => ρ₀ (X n)) atTop (𝓝 (ρ₀ Y))

/-- The minimal penalty of an unconditional risk measure (p. 7):
`α*₀(Q) = sup_{X ∈ L∞} {-E_Q X - ρ₀(X)} ∈ (-∞, +∞]`, a supremum of real numbers taken in
`EReal`. -/
noncomputable def minPenalty₀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ₀ : (Ω → ℝ) → ℝ) (Q : Measure Ω) : EReal :=
  ⨆ X : {X : Ω → ℝ // MemLp X ⊤ P}, ((-(∫ ω, X.1 ω ∂Q) - ρ₀ X.1 : ℝ) : EReal)

end CondConvexRisk.Representation
