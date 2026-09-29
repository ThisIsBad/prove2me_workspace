import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Lemma 5.1 (Uniqueness of SVM solutions), p. 167: let `L` be a convex loss, `H` be the RKHS of
a (measurable) kernel `k` over `X`, and `P` be a distribution on `X × ℝ` with `R_{L,P}(f) < ∞` for
some `f ∈ H`. Then for all `λ > 0` there is at most one general SVM solution, i.e. at most one
minimizer of `f ↦ λ‖f‖²_H + R_{L,P}(f)` over `H`. -/
theorem lemma_5_1_uniqueness_of_svm_solutions {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hfin : ∃ f : H, populationRisk L P (toFun f) < ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f1 f2 : H)
    (hf1 : ∀ g : H, ENNReal.ofReal (lam * ‖f1‖ ^ 2) + populationRisk L P (toFun f1) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g))
    (hf2 : ∀ g : H, ENNReal.ofReal (lam * ‖f2‖ ^ 2) + populationRisk L P (toFun f2) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    f1 = f2 := by sorry

end SupportVectorMachines.InfiniteSample
