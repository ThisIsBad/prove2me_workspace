import Mathlib

namespace SionMinimax.KKM
theorem remark_3_6 :
    let f : ℝ → ℝ → ℝ := fun μ ν =>
      if (0 ≤ μ ∧ μ < 1 / 2 ∧ ν = 0) ∨ (1 / 2 ≤ μ ∧ μ ≤ 1 ∧ ν = 1) then 0 else 1
    (∀ ν ∈ Set.Icc (0 : ℝ) 1, QuasiconcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun μ => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, QuasiconvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun ν => f μ ν)) ∧
    (∀ μ ∈ Set.Icc (0 : ℝ) 1, LowerSemicontinuousOn (fun ν => f μ ν) (Set.Icc (0 : ℝ) 1)) ∧
    ¬ UpperSemicontinuousOn (fun μ => f μ 1) (Set.Icc (0 : ℝ) 1) ∧
    (⨆ μ : Set.Icc (0 : ℝ) 1, ⨅ ν : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 0 ∧
    (⨅ ν : Set.Icc (0 : ℝ) 1, ⨆ μ : Set.Icc (0 : ℝ) 1, ((f μ ν : ℝ) : EReal)) = 1 := by sorry
end SionMinimax.KKM

