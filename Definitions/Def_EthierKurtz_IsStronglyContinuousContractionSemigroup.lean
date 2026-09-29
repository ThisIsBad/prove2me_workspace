import Mathlib

open Filter
open scoped Topology

namespace EthierKurtz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chapter 1, p. 6. Only nonnegative times are used; negative-time values
of this real-indexed family are immaterial. Strong continuity is at zero from
strictly positive times, exactly as in the source. -/
def IsStronglyContinuousContractionSemigroup (T : ℝ → E →L[ℝ] E) : Prop :=
  T 0 = ContinuousLinearMap.id ℝ E ∧
  (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
  (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
  (∀ x : E, Tendsto (fun t : ℝ => T t x) (𝓝[>] (0 : ℝ)) (𝓝 x))

end EthierKurtz
