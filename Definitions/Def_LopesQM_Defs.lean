import Mathlib

open MeasureTheory

namespace LopesQM

/-- Euclidean space `ℝⁿ`, carrying Lebesgue measure `volume`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Complex-valued wave functions `ψ : ℝⁿ → ℂ`. -/
abbrev WaveFn (n : ℕ) := Rn n → ℂ

/-- (Possibly unbounded) operators, acting on all functions `ℝⁿ → ℂ`;
domains are imposed separately as hypotheses. -/
abbrev Op (n : ℕ) := WaveFn n → WaveFn n

/-- Position operator `Xⱼ` (multiplication by the coordinate `xⱼ`). -/
def positionOp {n : ℕ} (j : Fin n) : Op n :=
  fun ψ x => ((x j : ℝ) : ℂ) * ψ x

/-- Momentum operator `Pⱼ = -iħ ∂/∂xⱼ` (Definição 1.20). -/
noncomputable def momentumOp {n : ℕ} (hbar : ℝ) (j : Fin n) : Op n :=
  fun ψ x => -(Complex.I * (hbar : ℂ)) * fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))

/-- Commutator `[A, B] = AB - BA` (Definição 3.1). -/
def commutator {n : ℕ} (A B : Op n) : Op n :=
  fun ψ => A (B ψ) - B (A ψ)

/-- The book's `L²` inner product `⟨φ, ψ⟩ = ∫ φ(x) conj(ψ(x)) dx`
(linear in the first argument, as in Chapter 1). -/
noncomputable def l2Inner {n : ℕ} (φ ψ : WaveFn n) : ℂ :=
  ∫ x, φ x * (starRingEnd ℂ) (ψ x)

/-- The `L²` norm `|ψ| = (∫ |ψ(x)|² dx)^{1/2}`. -/
noncomputable def l2Norm {n : ℕ} (ψ : WaveFn n) : ℝ :=
  Real.sqrt (∫ x, ‖ψ x‖ ^ 2)

/-- Expected value `E_ψ(A) = ⟨Aψ, ψ⟩ / ⟨ψ, ψ⟩` (Definição 8.1, p. 128). -/
noncomputable def expectation {n : ℕ} (A : Op n) (ψ : WaveFn n) : ℂ :=
  l2Inner (A ψ) ψ / l2Inner ψ ψ

/-- Dispersion `Δ_ψ(A) = |(A - E_ψ(A) I) ψ|` (Definição 8.2). -/
noncomputable def dispersion {n : ℕ} (A : Op n) (ψ : WaveFn n) : ℝ :=
  l2Norm (fun x => A ψ x - expectation A ψ * ψ x)

/-- Domain `D(Xⱼ)`: `ψ ∈ L²(ℝⁿ)` and `xⱼ ψ ∈ L²(ℝⁿ)`. -/
def InPositionDomain {n : ℕ} (j : Fin n) (ψ : WaveFn n) : Prop :=
  MemLp ψ 2 ∧ MemLp (positionOp j ψ) 2

/-- Domain `D(Pⱼ)`: `ψ` of class `C¹` with compact support (Definição 1.20). -/
def InMomentumDomain {n : ℕ} (ψ : WaveFn n) : Prop :=
  ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ

/-- Gaussian wave packet (Definição 8.3):
`ψ(x) = (2πa²)^{-n/4} exp(-|x - x₀|²/(4a²)) exp(i⟨p₀, x⟩/ħ)`. -/
noncomputable def gaussianPacket {n : ℕ} (hbar a : ℝ) (x0 p0 : Rn n) : WaveFn n :=
  fun x => (((2 * Real.pi * a ^ 2) ^ ((n : ℝ) / 4))⁻¹ : ℝ) *
    Complex.exp (((-(‖x - x0‖ ^ 2) / (4 * a ^ 2) : ℝ) : ℂ)) *
    Complex.exp (Complex.I * (((inner ℝ p0 x) / hbar : ℝ) : ℂ))

end LopesQM
