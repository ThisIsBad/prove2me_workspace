import Mathlib

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell's discounted dynamic programming data (Section 3, p. 228).
The state and action types are supplied with nonempty standard Borel structures in statements. -/
structure Problem (S A : Type*) [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] where
  q : Kernel (S × A) S
  q_markov : IsMarkovKernel q
  r : S × A × S → ℝ
  r_measurable : Measurable r
  r_bounded : ∃ C : ℝ, ∀ x, |r x| ≤ C
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

/-- The history before decision `n+1`: `n` completed state-action pairs and
the current state. The first decision has history `Hist S A 0`. -/
def Hist (S A : Type*) (n : ℕ) := (Fin n → S × A) × S

instance instMeasurableSpaceHist {S A : Type*} [MeasurableSpace S]
    [MeasurableSpace A] (n : ℕ) : MeasurableSpace (Hist S A n) :=
  inferInstanceAs (MeasurableSpace ((Fin n → S × A) × S))

/-- A randomized history-dependent plan: one probability kernel per decision. -/
structure Plan {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] where
  κ : (n : ℕ) → Kernel (Hist S A n) A
  κ_markov : ∀ n, IsMarkovKernel (κ n)

/-- A non-randomized Markov plan, given by measurable state-to-action rules. -/
def MarkovPlan (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] :=
  ℕ → {f : S → A // Measurable f}

/-- A bounded Borel (measurable) real-valued function. -/
def IsBM {S : Type*} [MeasurableSpace S] (u : S → ℝ) : Prop :=
  Measurable u ∧ ∃ C : ℝ, ∀ s, |u s| ≤ C

end DiscountedDP.Stationary
