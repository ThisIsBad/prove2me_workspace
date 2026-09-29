import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Theorem 5.5 (Representer theorem), p. 168: let `L` be a convex loss and
`D := ((x₁,y₁),…,(xₙ,yₙ)) ∈ (X × ℝ)ⁿ`. Let `H` be the RKHS of a kernel `k` over `X`. Then for all
`λ > 0` there exists a unique empirical SVM solution `f_{D,λ} ∈ H`, i.e. a unique minimizer of
`f ↦ λ‖f‖²_H + R_{L,D}(f)` over `H`; moreover there exist `α₁,…,αₙ ∈ ℝ` with
`f_{D,λ}(x) = ∑ᵢ αᵢ k(x,xᵢ)` for all `x ∈ X`. -/
theorem theorem_5_5_representer_theorem {X : Type*} {n : ℕ} (hn : 0 < n)
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (D : Fin n → X × ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃! f : H,
      (∀ g : H, lam * ‖f‖ ^ 2 + empiricalRisk n L D (toFun f) ≤
        lam * ‖g‖ ^ 2 + empiricalRisk n L D (toFun g)) ∧
      ∃ α : Fin n → ℝ, ∀ x : X, toFun f x = ∑ i, α i * k x (D i).1 := by sorry

end SupportVectorMachines.InfiniteSample

