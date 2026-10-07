import Mathlib

namespace SionMinimax.KKM
theorem lemma_3_3_prime {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (N : Set E) (hN : Convex ℝ N) (hne : N.Nonempty)
    (X : Finset ι) (f : ι → E → ℝ) (c : ℝ)
    (hq : ∀ x ∈ X, QuasiconvexOn ℝ N (fun ν => f x ν))
    (hl : ∀ x ∈ X, LowerSemicontinuousOn (fun ν => f x ν) N)
    (hP : ∀ ν ∈ N, ∃ x ∈ X, c < f x ν)
    (hmin : ∀ X' : Finset ι, X' ⊂ X → ¬ ∀ ν ∈ N, ∃ x ∈ X', c < f x ν) :
    ∃ ν₀ ∈ N, ∀ x ∈ X, c < f x ν₀ := by sorry
end SionMinimax.KKM

