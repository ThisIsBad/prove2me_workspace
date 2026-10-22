import Mathlib

namespace FriezeKannan.Continuum

open MeasureTheory

/-- The unit square `[0,1]²`, with Lebesgue (product) measure `volume = volume.prod volume`. -/
abbrev Sq := unitInterval × unitInterval

/-- `f(S, T) = ∫_{S×T} f(x, y) dx dy` (Frieze–Kannan §8, p. 217). -/
noncomputable def rectInt (f : Sq → ℝ) (S T : Set unitInterval) : ℝ :=
  ∫ p in S ×ˢ T, f p

/-- `‖f‖₂ = (∫_{[0,1]²} f(x, y)² dx dy)^{1/2}` (Frieze–Kannan §8, p. 217). -/
noncomputable def l2Norm (f : Sq → ℝ) : ℝ :=
  Real.sqrt (∫ p, f p ^ 2)

/-- The cut function `CUT(S, T, d)`: equal to `d` on `S × T` and `0` elsewhere
(Frieze–Kannan §8, p. 217). -/
noncomputable def cutFun (S T : Set unitInterval) (d : ℝ) : Sq → ℝ :=
  (S ×ˢ T).indicator (fun _ => d)

/-- The sum `f₁ + ⋯ + f_s` of the cut functions `f_t = CUT(S_t, T_t, d_t)`, `t ∈ Fin s`. -/
noncomputable def cutFunSum {s : ℕ} (Ss Ts : Fin s → Set unitInterval) (d : Fin s → ℝ) :
    Sq → ℝ :=
  fun p => ∑ t, cutFun (Ss t) (Ts t) (d t) p

end FriezeKannan.Continuum
