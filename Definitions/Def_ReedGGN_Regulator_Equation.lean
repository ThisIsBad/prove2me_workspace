import Mathlib

namespace ReedGGN.Regulator

open MeasureTheory

/-- The operator `Ψ^a_B` of the proof of Proposition 3.1 (p. 34):
`Ψ^a_B(u)(t) = ∫_0^t (u(t − s) + a)^+ dB(s)`. The cumulative distribution function `B` on `ℝ`
is represented by its law `μ` (so `B(t) = μ((−∞, t])`), and the Stieltjes integral is over
the closed interval `[0, t]`, an atom of `B` at `0` included (Appendix, p. 37). For `t < 0`
the interval is empty and the value is `0`. -/
noncomputable def psi (μ : Measure ℝ) (a : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Set.Icc 0 t, max (u (t - s) + a) 0 ∂μ

/-- `z` solves the regulator equation (3.1) (p. 9) with input `x`:
`z(t) = x(t) + ∫_0^t (z(t − s) + a)^+ dB(s)` for every `t ≥ 0`, with `B` the distribution
function of `μ` and the integral over the closed interval `[0, t]`. -/
def SolvesRegulator (μ : Measure ℝ) (a : ℝ) (x z : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → z t = x t + ∫ s in Set.Icc 0 t, max (z (t - s) + a) 0 ∂μ

/-- The successive approximations (A.3) (p. 32): `u_0 = 0` and
`u_{n+1}(t) = x(t) + ∫_0^t (u_n(t − s) + a)^+ dB(s)`. -/
noncomputable def picard (μ : Measure ℝ) (a : ℝ) (x : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun t => x t + psi μ a (picard μ a x n) t

end ReedGGN.Regulator
