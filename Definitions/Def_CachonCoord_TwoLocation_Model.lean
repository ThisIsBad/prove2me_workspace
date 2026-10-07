import Mathlib

open MeasureTheory ProbabilityTheory

namespace CachonCoord.TwoLocation

/-- The two-location base-stock model of Cachon (2003), §6.8.1–6.8.2, pp. 77–79 (after Cachon
and Zipkin 1999), with the single-location objects of §6.7.1, pp. 71–73, that it is built on.

`lawR` is the law of the retailer's lead-time demand `D_r` (over the retailer's lead time `L_r`),
`lawS` the law of the supplier's lead-time demand `D_s` (over `L_s`). Both are probability laws on
nonnegative demand with finite mean whose distribution functions `F_r`, `F_s` are continuous,
vanish at `0` (`D > 0`), are strictly increasing on `[0, ∞)` and differentiable on `(0, ∞)`
("assume F_s is increasing and differentiable", p. 77, and the analogue for `F_r` in §6.7.1).
`hr`, `hs` are the holding cost rates `h_r`, `h_s` with `0 < h_s < h_r` (p. 77); `br`, `bs` are
the backorder cost rates `β_r`, `β_s` charged to the retailer and to the supplier for backorders
at the retailer, both positive (footnote 34: the cases `β_s = 0` or `β_r = 0` "are not treated
here"). -/
structure Model where
  lawR : Measure ℝ
  probR : IsProbabilityMeasure lawR
  nonnegR : lawR (Set.Iio 0) = 0
  meanR : Integrable (id : ℝ → ℝ) lawR
  cdfR_zero : cdf lawR 0 = 0
  cdfR_strict : StrictMonoOn (cdf lawR) (Set.Ici 0)
  cdfR_cont : Continuous (cdf lawR)
  cdfR_diff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (cdf lawR) y
  lawS : Measure ℝ
  probS : IsProbabilityMeasure lawS
  nonnegS : lawS (Set.Iio 0) = 0
  meanS : Integrable (id : ℝ → ℝ) lawS
  cdfS_zero : cdf lawS 0 = 0
  cdfS_strict : StrictMonoOn (cdf lawS) (Set.Ici 0)
  cdfS_cont : Continuous (cdf lawS)
  cdfS_diff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ (cdf lawS) y
  hr : ℝ
  hs : ℝ
  br : ℝ
  bs : ℝ
  hs_pos : 0 < hs
  hs_lt_hr : hs < hr
  br_pos : 0 < br
  bs_pos : 0 < bs

namespace Model

variable (M : Model)

/-! ### Single-location objects (§6.7.1, pp. 72–73), at retailer inventory level `y` -/

/-- `F_r(y)`, the distribution function of the retailer's lead-time demand. -/
noncomputable def FR (y : ℝ) : ℝ := cdf M.lawR y

/-- `F_s(y)`, the distribution function of the supplier's lead-time demand. -/
noncomputable def FS (y : ℝ) : ℝ := cdf M.lawS y

/-- `μ_r = E[D_r]`. -/
noncomputable def muR : ℝ := ∫ x, x ∂M.lawR

/-- `μ_s = E[D_s]` (p. 77). -/
noncomputable def muS : ℝ := ∫ x, x ∂M.lawS

/-- `I_r(y) = E[(y − D_r)⁺]`, the retailer's expected on-hand inventory at level `y` (28). -/
noncomputable def IR (y : ℝ) : ℝ := ∫ x, max (y - x) 0 ∂M.lawR

/-- `B_r(y) = E[(D_r − y)⁺]`, the retailer's expected backorders at level `y` (29). -/
noncomputable def BR (y : ℝ) : ℝ := ∫ x, max (x - y) 0 ∂M.lawR

/-- `β = β_r + β_s`. -/
def beta : ℝ := M.br + M.bs

/-- `c_r(y) = h_r I_r(y) + β_r B_r(y)`, the retailer's retail-level cost rate (p. 73). -/
noncomputable def cR (y : ℝ) : ℝ := M.hr * M.IR y + M.br * M.BR y

/-- `c_s(y) = β_s B_r(y)`, the supplier's retail-level cost rate (p. 73). -/
noncomputable def cS (y : ℝ) : ℝ := M.bs * M.BR y

/-- `c(y) = c_r(y) + c_s(y)`, the chain's retail-level cost rate (30). -/
noncomputable def c (y : ℝ) : ℝ := M.cR y + M.cS y

/-- `c'(y) = (h_r + β) F_r(y) − β`, the derivative of `c` written out (the expression whose
equation `c'(y) = h_s` is (37) and whose root is (31)). It is a plain function here; that it
is the derivative of `c` is a theorem, not part of the definition. -/
noncomputable def cDeriv (y : ℝ) : ℝ := (M.hr + M.beta) * M.FR y - M.beta

/-! ### Two-location objects (§6.8.2, pp. 78–79) -/

/-- The retail-level average of a single-location function `g` under base stocks
`(s_r, s_s)`: the retailer's inventory level is `s_r − (D_s − s_s)⁺`, so
`g(s_r, s_s) = E[g(s_r − (D_s − s_s)⁺)] = F_s(s_s) g(s_r) + ∫_{s_s}^∞ g(s_r + s_s − x) f_s(x) dx`
(p. 78). Defined by the expectation. -/
noncomputable def atRetail (g : ℝ → ℝ) (sr ss : ℝ) : ℝ :=
  ∫ x, g (sr - max (x - ss) 0) ∂M.lawS

/-- `I_r(s_r, s_s)`, the retailer's average inventory (p. 79). -/
noncomputable def IR2 (sr ss : ℝ) : ℝ := M.atRetail M.IR sr ss

/-- `B_r(s_r, s_s)`, the retailer's average backorders (p. 79). -/
noncomputable def BR2 (sr ss : ℝ) : ℝ := M.atRetail M.BR sr ss

/-- `c_r(s_r, s_s)`, the rate at which the retailer incurs costs at the retail level (p. 78). -/
noncomputable def cR2 (sr ss : ℝ) : ℝ := M.atRetail M.cR sr ss

/-- `c_s(s_r, s_s)`, the rate at which the supplier incurs costs at the retail level (p. 78). -/
noncomputable def cS2 (sr ss : ℝ) : ℝ := M.atRetail M.cS sr ss

/-- `c(s_r, s_s) = c_r(s_r, s_s) + c_s(s_r, s_s)` (p. 78). -/
noncomputable def c2 (sr ss : ℝ) : ℝ := M.cR2 sr ss + M.cS2 sr ss

/-- `I_s(y)`, the supplier's average on-hand inventory at base stock `y`, `E[(y − D_s)⁺]`;
it equals `∫_0^y F_s(x) dx` (p. 79). -/
noncomputable def IS (y : ℝ) : ℝ := ∫ x, max (y - x) 0 ∂M.lawS

/-- `B_s(y) = μ_s − y + I_s(y)`, the supplier's average backorder (p. 82). -/
noncomputable def BS (y : ℝ) : ℝ := M.muS - y + M.IS y

/-- `π_r(s_r, s_s) = c_r(s_r, s_s)`, the retailer's total average cost rate (p. 79). -/
noncomputable def piR (sr ss : ℝ) : ℝ := M.cR2 sr ss

/-- `π_s(s_r, s_s) = h_s I_s(s_s) + c_s(s_r, s_s)`, the supplier's average cost (p. 79). -/
noncomputable def piS (sr ss : ℝ) : ℝ := M.hs * M.IS ss + M.cS2 sr ss

/-- `Π(s_r, s_s) = π_r(s_r, s_s) + π_s(s_r, s_s)`, the supply chain's total cost (p. 79). -/
noncomputable def Pi (sr ss : ℝ) : ℝ := M.piR sr ss + M.piS sr ss

end Model
end CachonCoord.TwoLocation
