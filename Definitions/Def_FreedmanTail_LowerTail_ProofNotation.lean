import Mathlib
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.14), p. 109: `φ(λ) = λ²/2 − λ³/6`.
The page prints `φ(λ) = λ²/2 > λ³/6`; the `>` is a misprint for `−` (the proof uses
`0 < φ < f`, `φ(λ)(1 − 2δ)b < ½λ²(1 − 2δ)b` and the factor `exp[⅙λ³(1 − 2δ)b]` of (4.20)). -/
noncomputable def phi (lam : ℝ) : ℝ := lam ^ 2 / 2 - lam ^ 3 / 6

/-- Freedman (1975), (4.14), p. 109: `λ = (1 + δ) a / b`. -/
noncomputable def lamStar (δ a b : ℝ) : ℝ := (1 + δ) * a / b

/-- Freedman (1975), (4.14), p. 109: `k = a²/b`. -/
noncomputable def kStar (a b : ℝ) : ℝ := a ^ 2 / b

/-- Freedman (1975), (4.14), p. 109: `N = 2/δ²`. -/
noncomputable def NStar (δ : ℝ) : ℝ := 2 / δ ^ 2

/-- Freedman (1975), p. 109: `I₁ = [0, Na]`. -/
noncomputable def I1 (δ a : ℝ) : Set ℝ := Set.Icc 0 (NStar δ * a)

/-- Freedman (1975), p. 109: `I₂ = (Na, (1 − 2δ)b]`. -/
noncomputable def I2 (δ a b : ℝ) : Set ℝ := Set.Ioc (NStar δ * a) ((1 - 2 * δ) * b)

/-- Freedman (1975), p. 109: `I₃ = (b, 2b]`. -/
def I3 (b : ℝ) : Set ℝ := Set.Ioc b (2 * b)

/-- Freedman (1975), p. 109: `I₄ = (2b, ∞)`. -/
def I4 (b : ℝ) : Set ℝ := Set.Ioi (2 * b)

/-- Freedman (1975), p. 109: `I₅ = ((1 − 2δ)b, b]`. -/
def I5 (δ b : ℝ) : Set ℝ := Set.Ioc ((1 - 2 * δ) * b) b

/-- Freedman (1975), p. 109:
`η_I = φ(λ) ∫_I P{W < x} exp[−φ(λ)x] dx` with `λ = (1 + δ)a/b`, for an interval `I`
(the page's `η_i` is `eta P W δ a b I_i`). The integrand is a monotone function of `x`
times `exp[−φ(λ)x]`, hence measurable. -/
noncomputable def eta {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ)
    (δ a b : ℝ) (I : Set ℝ) : ℝ :=
  phi (lamStar δ a b) *
    ∫ x in I, P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))

end FreedmanTail.LowerTail
