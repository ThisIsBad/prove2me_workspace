import Mathlib

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

/-- The partial sums `S_n = X_1 + ⋯ + X_n` of a sequence of random variables. -/
def partialSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, X i ω

/-- The series `∑ X_n` **converges almost surely**: for almost every `ω` the partial sums
`S_N(ω)` converge to some real limit.  Durrett, *Probability: Theory and Examples*, section 2.5. -/
def SeriesConvergesAE {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun N => partialSum X N ω) atTop (nhds L)

/-- The truncation `Y = X · 1(|X| ≤ A)` used in Kolmogorov's three-series theorem. -/
noncomputable def truncate {Ω : Type*} (A : ℝ) (X : Ω → ℝ) : Ω → ℝ := fun ω => if |X ω| ≤ A then X ω else 0

/-- A **finite permutation** of `ℕ`: a bijection moving only finitely many indices. -/
def FinitelySupported (σ : Equiv.Perm ℕ) : Prop := ∀ᶠ i in Filter.cofinite, σ i = i

/-- A **permutable** (exchangeable) event: a measurable set of sequences whose occurrence is
unaffected by rearranging finitely many coordinates.  These form the exchangeable σ-field `ℰ` of
Durrett, section 2.5. -/
def IsPermutable {S : Type*} [MeasurableSpace S] (A : Set (ℕ → S)) : Prop :=
  MeasurableSet A ∧ ∀ σ : Equiv.Perm ℕ, FinitelySupported σ → (fun ω => ω ∘ σ) ⁻¹' A = A

end DurrettProbability
