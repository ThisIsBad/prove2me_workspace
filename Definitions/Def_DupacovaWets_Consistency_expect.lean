import Mathlib
open MeasureTheory
open scoped ENNReal

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 10, (3.2) and (3.6), with the convention of p. 10:
the expectation `E_Q g = ∫ g dQ` of an extended-real-valued function `g`, set equal to `+∞`
whenever `g` is not bounded above by a summable function (`∫ g⁺ dQ = ∞`), and equal to
`∫ g⁺ dQ - ∫ g⁻ dQ` otherwise (which is `-∞` when `∫ g⁻ dQ = ∞`). -/
noncomputable def expect {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ) (g : Ξ → EReal) :
    EReal :=
  if ∫⁻ ξ, (g ξ).toENNReal ∂Q = ∞ then ⊤
  else ((∫⁻ ξ, (g ξ).toENNReal ∂Q : ℝ≥0∞) : EReal) - ((∫⁻ ξ, (-g ξ).toENNReal ∂Q : ℝ≥0∞) : EReal)

/-- The expectation functional `x ↦ E_Q f(x, ·)` on `ℝⁿ`: `Ef = expectFn P f` (3.2) and
`E^ν f(·, ζ) = expectFn (P^ν(·, ζ)) f` (3.6). -/
noncomputable def expectFn {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) : EuclideanSpace ℝ (Fin n) → EReal :=
  fun x => expect Q (f x)

end DupacovaWets.Consistency
