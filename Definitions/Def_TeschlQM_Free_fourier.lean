import Mathlib

namespace TeschlQM.Free

open MeasureTheory FourierTransform
open scoped InnerProductSpace

/-- Teschl (7.3), p. 161: the Fourier transform in Teschl's normalization,
`F(f)(p) = f̂(p) = (2π)^{-n/2} ∫_{ℝⁿ} e^{-ipx} f(x) dⁿx`, on `ℝⁿ = EuclideanSpace ℝ (Fin n)`
(so `px = ⟪p, x⟫` and `x² = ‖x‖²` are Euclidean). This is **not** Mathlib's `𝓕`, which uses
`e^{-2πi⟪x, ξ⟫}` and no prefactor. For `f` not integrable the Bochner integral is `0`. -/
noncomputable def fourier (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (p : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    ∫ x : EuclideanSpace ℝ (Fin n), Complex.exp (-(⟪p, x⟫_ℝ : ℂ) * Complex.I) * f x

/-- Teschl (7.8), p. 163: the inverse Fourier transform in Teschl's normalization,
`F⁻¹(g)(x) = ǧ(x) = (2π)^{-n/2} ∫_{ℝⁿ} e^{ipx} g(p) dⁿp`. -/
noncomputable def fourierInv (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    ∫ p : EuclideanSpace ℝ (Fin n), Complex.exp ((⟪p, x⟫_ℝ : ℂ) * Complex.I) * g p

/-- Teschl, p. 164 (Theorem 7.5, (7.10)): the Fourier transform `ψ̂` of `ψ ∈ L²(ℝⁿ)` in Teschl's
normalization, obtained from Mathlib's unitary `L²` Fourier transform `𝓕` (normalization
`e^{-2πi⟪x, ξ⟫}`) through the rescaling identity `ψ̂(p) = (2π)^{-n/2} (𝓕ψ)(p / (2π))`.
The value is a function `ℝⁿ → ℂ`, determined up to a null set (it is built from an almost
everywhere defined representative of `𝓕ψ`). -/
noncomputable def fourierL2 (n : ℕ)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (p : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ *
    (𝓕 ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ((2 * Real.pi)⁻¹ • p)

end TeschlQM.Free
