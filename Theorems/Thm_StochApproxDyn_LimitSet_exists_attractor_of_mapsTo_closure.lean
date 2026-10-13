import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Lemma 5.2 (Benaïm 1999, p. 22): if `U ⊂ M` is a nonempty open set with compact closure and
`Φ_T(Ū) ⊂ U` for some `T > 0`, then there is an attractor `A ⊂ U` whose basin contains `Ū`. -/
theorem exists_attractor_of_mapsTo_closure {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U : Set M) (hUo : IsOpen U) (hUne : U.Nonempty) (hUc : IsCompact (closure U))
    (T : ℝ≥0) (hT : 0 < T) (hTU : Φ T '' closure U ⊆ U) :
    ∃ A : Set M, IsAttractor Φ A ∧ A ⊆ U ∧ closure U ⊆ basin Φ A := by sorry

end StochApproxDyn.LimitSet

