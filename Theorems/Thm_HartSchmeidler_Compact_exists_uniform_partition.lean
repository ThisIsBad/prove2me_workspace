import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 25, the general case: for continuous `hⁱ` on the compact `S` and
`ε > 0`, `Sⁱ` has a finite partition into nonempty Borel sets `A₁, …, A_K` such that
`|hⁱ(s⁻ⁱ, a) − hⁱ(s⁻ⁱ, b)| < ε` whenever `a, b` lie in the same `A_k`, for every `s⁻ⁱ`. -/
theorem exists_uniform_partition {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (A : Fin K → Set (S i)),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, (A k).Nonempty) ∧ Pairwise (Function.onFun Disjoint A) ∧
        (⋃ k, A k) = Set.univ ∧
        ∀ k, ∀ a ∈ A k, ∀ b ∈ A k, ∀ s : Profile S,
          |h i (Function.update s i a) - h i (Function.update s i b)| < ε := by sorry

end HartSchmeidler.Compact

