import Mathlib

/-!
# Microstate counting in dS₃ (Collier–Eberhardt–Mühlmann, arXiv:2501.01486)

Definitions for §4.4 and Appendix C of "A microscopic realization of dS₃".
The Liouville parameter `b` is a complex number with `-i b² ∈ ℝ_{>0}` (footnote 2),
so that the central charge `c = 1 + 6 (b + b⁻¹)²` lies in `13 + iℝ`.
-/

noncomputable section

namespace DS3Micro

open Complex

/-- The parameter regime of the paper (footnote 2): `-i b² ∈ ℝ_{>0}`, i.e. `b² = i β`
for some real `β > 0`. -/
def InRegime (b : ℂ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ b ^ 2 = Complex.I * (β : ℂ)

/-- Leading density of eigenvalues of the first matrix, eq. (C.4):
`ρ₀(E) = (2/π) sinh(-iπ b²) sin(-i b² arccosh(E/2))`. -/
def rho0 (b : ℂ) (E : ℝ) : ℂ :=
  (2 / (Real.pi : ℂ)) * Complex.sinh (-Complex.I * (Real.pi : ℂ) * b ^ 2) *
    Complex.sin (-Complex.I * b ^ 2 * (Real.arcosh (E / 2) : ℂ))

/-- The first zero of the eigenvalue density, `E₀ = 2 cos(π b⁻²)` (§4.4, Appendix C). -/
def E0 (b : ℂ) : ℂ :=
  2 * Complex.cos ((Real.pi : ℂ) * (b ^ 2)⁻¹)

/-- Effective number of eigenvalues, eq. (4.32): `N_eff = ∫_2^{E₀} e^{S₀} ρ₀(E) dE`.
The upper limit is the real part of `E₀` (which is real in the regime `InRegime b`). -/
def Neff (b : ℂ) (S0 : ℝ) : ℂ :=
  ∫ E in (2 : ℝ)..(E0 b).re, (Real.exp S0 : ℂ) * rho0 b E

/-- Microscopic de Sitter entropy, eq. (4.33): `S_dS^micro = 2 log N_eff`
(complex principal logarithm). -/
def SdSMicro (b : ℂ) (S0 : ℝ) : ℂ :=
  2 * Complex.log (Neff b S0)

/-- Reduced tension of the first ZZ-instanton, eq. (4.34):
`T̂₁,₁ = 8 b² sin(π b²) sin(π b⁻²) / (1 - b⁴)`. -/
def tensionHat (b : ℂ) : ℂ :=
  8 * b ^ 2 * Complex.sin ((Real.pi : ℂ) * b ^ 2) * Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
    (1 - b ^ 4)

/-- Tension of the first ZZ-instanton, eq. (4.34): `T₁,₁ = e^{S₀} T̂₁,₁`. -/
def tension (b : ℂ) (S0 : ℝ) : ℂ :=
  (Real.exp S0 : ℂ) * tensionHat b

/-- Normalization of the string path integral on the sphere, eq. (4.4):
`C_{S²} = 32 π⁴ (sin(π b²) sin(π b⁻²) / (b² - b⁻²))²`. -/
def CS2 (b : ℂ) : ℂ :=
  32 * (Real.pi : ℂ) ^ 4 *
    (Complex.sin ((Real.pi : ℂ) * b ^ 2) * Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
      (b ^ 2 - (b ^ 2)⁻¹)) ^ 2

end DS3Micro

end
