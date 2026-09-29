import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Theorem 5.6 (Non-trivial SVM solutions), p. 168: let `L` be a convex loss and `P` be a
distribution on `X × ℝ` such that `L` is a `P`-integrable Nemitski loss. Let `H` be the RKHS of a
bounded (measurable) kernel `k` over `X` with `R*_{L,P,H} := inf_{f∈H} R_{L,P}(f) < R_{L,P}(0)`.
Then for all `λ > 0`, every general SVM solution `f_{P,λ}` is nonzero. -/
theorem theorem_5_6_non_trivial_svm_solutions {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (hgap : (⨅ f : H, populationRisk L P (toFun f)) < populationRisk L P (fun _ => 0))
    (lam : ℝ) (hlam : 0 < lam) (fPlam : H)
    (hmin : ∀ g : H, ENNReal.ofReal (lam * ‖fPlam‖ ^ 2) + populationRisk L P (toFun fPlam) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    fPlam ≠ 0 := by sorry

end SupportVectorMachines.InfiniteSample
