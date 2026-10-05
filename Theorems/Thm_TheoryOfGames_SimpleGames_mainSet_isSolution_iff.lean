import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

namespace TheoryOfGames.SimpleGames

/-- (50:J), p. 442: for a simple game in the reduced form with `γ = 1` (`v((i)) = -1`), a set
`U ⊆ W^m` and numbers `xᵢ` with (50:7) `xᵢ ≧ 0` and (50:8) `∑_{i in S} xᵢ = n` for `S` in
`U`, the set `V` of the `α^S`, `S` in `U`, is a solution if and only if, calling `i`
indifferent when `xᵢ = 0`: (50:8*) `∑_{i in T} xᵢ = n` for the `T` of `U` and for those which
differ from these only by indifferent elements; and (50:9*) `∑_{i in T} xᵢ > n` for all other
`T` of `U⁺`. -/
theorem mainSet_isSolution_iff {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1)
    (U : Set (Finset (Fin n))) (hU : U ⊆ minimalSets (winningSets v))
    (x : Fin n → ℝ) (hx7 : ∀ i, 0 ≤ x i) (hx8 : ∀ S ∈ U, ∑ i ∈ S, x i = (n : ℝ)) :
    IsSolution v (mainSet U x) ↔
      ((∀ T : Finset (Fin n), (∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          ∑ i ∈ T, x i = (n : ℝ)) ∧
        (∀ T ∈ uPlus U, (¬ ∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          (n : ℝ) < ∑ i ∈ T, x i)) := by sorry

end TheoryOfGames.SimpleGames

