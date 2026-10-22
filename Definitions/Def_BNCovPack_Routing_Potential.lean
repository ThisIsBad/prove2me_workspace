import Mathlib

namespace BNCovPack.Routing

/-- `u(min) = min_e u(e)`, the minimum edge capacity (p. 15). -/
noncomputable def uMin {E : Type*} [Fintype E] [Nonempty E] (u : E → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty u

/-- The rounding scale `B = exp(1 + ln(2m)/u(min)) − 1` of §5.2 (p. 15), where `m = |E|` is the
number of edges. -/
noncomputable def roundingScale {E : Type*} [Fintype E] [Nonempty E] (u : E → ℝ) : ℝ :=
  Real.exp (1 + Real.log (2 * (Fintype.card E : ℝ)) / uMin u) - 1

/-- The online potential `Φ = Φ₁ + Φ₂` of §5.2 (p. 15), as a function of the rounding scale `B`,
the total fractional flow `T = ∑_{r_i} ∑_P f(r_i, P)`, the edge loads `L e = ∑_{P ∋ e} ∑_{r_i}
f(r_i, P)`, the integral edge usage `χ e = χ(e)` (number of chosen paths using `e`) and the
number `s = ∑_{r_i} χ(r_i)` of served requests:

`Φ₁ = (1/2) exp(T/(2B) − ln 2 · s)`,
`Φ₂ = (1/(2m)) ∑_{e ∈ E} exp((1 + ln(2m)/u(e)) χ(e) − L e)`, with `m = |E|`. -/
noncomputable def potential {E : Type*} [Fintype E] (u : E → ℝ) (B T : ℝ) (L : E → ℝ)
    (χ : E → ℕ) (s : ℕ) : ℝ :=
  (1 / 2) * Real.exp (T / (2 * B) - Real.log 2 * (s : ℝ)) +
    (1 / (2 * (Fintype.card E : ℝ))) *
      ∑ e, Real.exp ((1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) * (χ e : ℝ) - L e)

end BNCovPack.Routing
