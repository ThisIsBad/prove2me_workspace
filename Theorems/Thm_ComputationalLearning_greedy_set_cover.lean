import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory


namespace ComputationalLearning

/-- **The greedy set cover bound** (§2.3, p. 39; Chvátal 1979). Let `𝒮` be a collection of subsets
of the finite universe `U` that covers `U`, and let `t` be a run of the greedy heuristic. Then
after `i` steps at most `(1 − 1/opt(𝒮))^i |U|` elements are uncovered, and all the elements of
`U` are covered after the heuristic has chosen `opt(𝒮) ln|U|` sets (at least one). -/
theorem greedy_set_cover {U : Type*} [DecidableEq U] [Fintype U] (𝒮 : Finset (Finset U))
    (hcov : IsCover 𝒮 𝒮) (t : ℕ → Finset U) (ht : IsGreedySequence 𝒮 t) :
    (∀ i : ℕ, ((uncovered t i).card : ℝ) ≤
      (1 - 1 / (optCover 𝒮 : ℝ)) ^ i * (Fintype.card U : ℝ)) ∧
    (∀ i : ℕ, 1 ≤ i → (optCover 𝒮 : ℝ) * Real.log (Fintype.card U) ≤ i →
      uncovered t i = ∅) := by sorry

end ComputationalLearning

