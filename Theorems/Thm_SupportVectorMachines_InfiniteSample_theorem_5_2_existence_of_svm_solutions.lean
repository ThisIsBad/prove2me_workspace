import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- Theorem 5.2 (Existence of SVM solutions), p. 167: let `L` be a convex loss and `P` be a
distribution on `X × ℝ` such that `L` is a `P`-integrable Nemitski loss. Let `H` be the RKHS of a
bounded (measurable) kernel `k` over `X`. Then for all `λ > 0` there exists a general SVM
solution, i.e. a minimizer of `f ↦ λ‖f‖²_H + R_{L,P}(f)` over `H`. -/
theorem theorem_5_2_existence_of_svm_solutions {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ f : H, ∀ g : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + populationRisk L P (toFun f) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g) := by sorry

end SupportVectorMachines.InfiniteSample

