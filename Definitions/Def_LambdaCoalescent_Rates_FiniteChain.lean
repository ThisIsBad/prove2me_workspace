import Mathlib

namespace LambdaCoalescent.Rates

open MeasureTheory
open scoped BigOperators NNReal

/-- Finite-dimensional distributions of a continuous-time finite-state chain with generator `Q`. -/
def IsRateChain {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]
    [Fintype S] [DecidableEq S] (P : Measure Ω) (Q : Matrix S S ℝ) (s₀ : S)
    (X : ℝ≥0 → Ω → S) : Prop :=
  (∀ t, Measurable (X t)) ∧
  ∀ (k : ℕ) (t : Fin (k + 1) → ℝ≥0), t 0 = 0 → Monotone t →
    ∀ s : Fin (k + 1) → S,
      P.real {ω | ∀ i, X (t i) ω = s i} =
        (if s 0 = s₀ then 1 else 0) *
          ∏ i : Fin k,
            NormedSpace.exp (((t i.succ : ℝ) - (t i.castSucc : ℝ)) • Q)
              (s i.castSucc) (s i.succ)

end LambdaCoalescent.Rates
