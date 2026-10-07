import Mathlib

namespace SionMinimax.KKM
theorem lemma_3_3 {E ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (M : Set E) (hM : Convex ℝ M) (hne : M.Nonempty)
    (Y : Finset ι) (f : E → ι → ℝ) (c : ℝ)
    (hq : ∀ y ∈ Y, QuasiconcaveOn ℝ M (fun μ => f μ y))
    (hu : ∀ y ∈ Y, UpperSemicontinuousOn (fun μ => f μ y) M)
    (hP : ∀ μ ∈ M, ∃ y ∈ Y, f μ y < c)
    (hmin : ∀ Y' : Finset ι, Y' ⊂ Y → ¬ ∀ μ ∈ M, ∃ y ∈ Y', f μ y < c) :
    ∃ μ₀ ∈ M, ∀ y ∈ Y, f μ₀ y < c := by sorry
end SionMinimax.KKM

