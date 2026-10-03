import Mathlib
import Definitions.Def_TeschlQM_Free_fourier

namespace TeschlQM.Free

/-- Teschl, Theorem 7.4, p. 163: the Fourier transform (Teschl's normalization (7.3)) is a bijection
of the Schwartz space `𝒮(ℝⁿ)` onto itself, its inverse is the transform `F⁻¹` of (7.8)
(`fourierInv`), `F²(f)(x) = f(-x)`, and hence `F⁴ = I`. -/
theorem fourier_schwartz_bijective (n : ℕ) :
    (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∃ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ⇑g = fourier n f) ∧
      (∀ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ∃ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, fourier n f = ⇑g) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        fourierInv n (fourier n f) = ⇑f ∧ fourier n (fourierInv n f) = ⇑f) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, fourier n (fourier n f) x = f (-x)) ∧
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        fourier n (fourier n (fourier n (fourier n f))) = ⇑f) := by sorry

end TeschlQM.Free
