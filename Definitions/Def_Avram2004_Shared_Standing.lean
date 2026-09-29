import Mathlib

open MeasureTheory
open scoped NNReal

namespace Avram2004.Shared

/-- Almost every path of `X` has bounded variation on every compact interval `[0, t]`. -/
def BoundedVar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0, eVariationOn (fun r => X r ω) (Set.Icc 0 t) ≠ ⊤

/-- Condition (AC): the Lévy measure `Λ` is absolutely continuous with respect to Lebesgue measure.
It is stated through the jumps of `X`: for every Lebesgue-null Borel set `A`, almost surely no
nonzero jump `ΔX_t = X_t - X_{t-}` with `t ∈ (0, 1]` lands in `A`. (`Λ(A \ {0})` is the expected number
of such jumps, and that number is Poisson distributed, so `Λ(A \ {0}) = 0` iff almost surely there is
none.) -/
def LevyAC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ A : Set ℝ, MeasurableSet A → volume A = 0 →
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ≥0) 1,
      X t ω - Function.leftLim (fun r => X r ω) t ∉ A \ {0}

/-- The standing assumption of the paper (§2, p. 216): `X` has unbounded variation, or `X` has
bounded variation and satisfies (AC). Since the paths of a Lévy process are either almost surely of
bounded variation or almost surely not, this is the implication "bounded variation → (AC)". -/
def Standing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  BoundedVar P X → LevyAC P X

end Avram2004.Shared
