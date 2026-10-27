import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem theorem_2_1
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] {N : ℕ} (U : G →* Matrix.unitaryGroup (Fin N) ℂ)
    (hU : Continuous U) (d : ℕ)
    {m : ℕ} (a : Fin m → ((Fin d → Fin N) → ℂ)) (ha : LinearIndependent ℂ a)
    (hspan : Submodule.span ℂ (Set.range a) = invariants U d)
    (i j : Fin d → Fin N) :
    ∫ g, ∏ x : Fin d, (U g : Matrix (Fin N) (Fin N) ℂ) (i x) (j x) ∂μ
      = ∑ x : Fin m, ∑ y : Fin m,
          coordMatrix a i x * weingartenMatrix a x y * (coordMatrix a)ᴴ y j := by sorry

end WeingartenCalc.Fundamental

