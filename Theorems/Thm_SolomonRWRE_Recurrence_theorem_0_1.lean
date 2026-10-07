import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), p. 2,
Theorem (0.1): a property of paths that holds `M_α`-almost surely for almost every fixed
environment `α` holds almost surely for the random walk in a random environment.

**Formalization Note.** The paper's path set `Ω ⊂ Z^N` is `S` here (the name `Ω` is taken by
the sample space). "`M_α({X_n} ∈ S) = 1`" is read as: every probability measure `ν` on path
space under which the coordinate process is the chain `M_α` started at `0` gives `S` measure
`1`. "For a.e. environment" is with respect to the environment law `Q = P.map (env α)`. -/
theorem theorem_0_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (S : Set (ℕ → ℤ)) (hS : MeasurableSet S)
    (h : ∀ᵐ a ∂(P.map (env α)), ∀ ν : Measure (ℕ → ℤ), IsProbabilityMeasure ν →
      IsChainInEnv ν a 0 (fun n w => w n) → ν S = 1) :
    P {ω | (fun n => X n ω) ∈ S} = 1 := by sorry

end SolomonRWRE.Recurrence

