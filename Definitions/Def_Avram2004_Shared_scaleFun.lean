import Mathlib

open MeasureTheory

namespace Avram2004.Shared

/-- Definition 1: `Φ(q)`, the largest root of `φ(θ) = q`, for an exponent `φ` (the Laplace exponent
`ψ` or one of its tilts `ψ_c`). For `q ≥ 0` the largest root is `≥ 0` (as `φ(0) = 0 ≤ q` and
`φ(θ) → ∞`), so restricting to `θ ≥ 0` does not change it. -/
noncomputable def Phi (φ : ℝ → ℝ) (q : ℝ) : ℝ :=
  sSup {θ : ℝ | 0 ≤ θ ∧ φ θ = q}

/-- The defining property of the `q`-scale function of Definition 2 for the exponent `φ`:
`W : ℝ → [0, ∞)`, identically zero on `(-∞, 0]`, continuous on `(0, ∞)`, with Laplace transform
`∫_0^∞ e^{-θx} W(x) dx = (φ(θ) - q)⁻¹` for every `θ > Φ(q)` (the integral converging absolutely). -/
def IsScaleFun (φ : ℝ → ℝ) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ W x) ∧ (∀ x ≤ 0, W x = 0) ∧ ContinuousOn W (Set.Ioi 0) ∧
    ∀ θ > Phi φ q, IntegrableOn (fun x => Real.exp (-θ * x) * W x) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi 0, Real.exp (-θ * x) * W x = (φ θ - q)⁻¹

/-- Definition 2: the `q`-scale function `W^{(q)}` of the exponent `φ`, i.e. the unique function with
the properties of `IsScaleFun` (the paper asserts existence and uniqueness; the constant `0` is only
a placeholder for the case where no such function exists). -/
noncomputable def scaleFun (φ : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  open Classical in if h : ∃ W, IsScaleFun φ q W then h.choose else 0

/-- Convolution powers on `[0, ∞)`: `convPow W k` is the `(k+1)`-th convolution power `W^{⋆(k+1)}`,
with `W^{⋆1} = W` and `W^{⋆(k+2)}(x) = ∫_0^x W^{⋆(k+1)}(x - y) W(y) dy`. -/
noncomputable def convPow (W : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => W
  | k + 1 => fun x => ∫ y in (0 : ℝ)..x, convPow W k (x - y) * W y

/-- The scale function `W^{(q)}` for every real `q`: Definition 2 when `q ≥ 0`, and the paper's
extension (5), `W^{(q)}(x) = ∑_{k ≥ 0} q^k W^{⋆(k+1)}(x)` with `W = W^{(0)}`, when `q < 0`. -/
noncomputable def scaleFunExt (φ : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  fun x => if 0 ≤ q then scaleFun φ q x
    else ∑' k : ℕ, q ^ k * convPow (scaleFun φ 0) k x

/-- Definition 3, (6): `Z^{(q)}(x) = 1 + q ∫_{-∞}^x W^{(q)}(z) dz`, for every real `q`
(with the extended `W^{(q)}` when `q < 0`). -/
noncomputable def scaleZ (φ : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  fun x => 1 + q * ∫ z in Set.Iic x, scaleFunExt φ q z

end Avram2004.Shared
