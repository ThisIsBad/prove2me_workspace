import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex

open MeasureTheory

namespace GallegoOzerADI.PositiveSetup

theorem abConvex_expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f : ℝ → (Fin n → ℝ) → ℝ) (hf : ∀ y, ABConvex a b (fun x => f x y))
    (D : Ω → ℝ) (Y : Ω → (Fin n → ℝ))
    (hint : ∀ x, Integrable (fun ω => f (x - D ω) (Y ω)) P) :
    ABConvex a b (fun x => ∫ ω, f (x - D ω) (Y ω) ∂P) := by sorry

end GallegoOzerADI.PositiveSetup
