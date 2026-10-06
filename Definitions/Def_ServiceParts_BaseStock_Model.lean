import Mathlib

open MeasureTheory Set

namespace ServiceParts.BaseStock

/-- The single-location, periodic-review, backorder model of Muckstadt (2005), Section 2.1,
pp. 16–19, with its standing assumptions: unit purchase cost `c`, unit holding cost `h`,
unit backorder cost `b`, discount factor `α`, and a demand density `g` on `(0, ∞)` that is
positive and continuous there, integrates to one, and has a finite mean. -/
structure Model where
  /-- unit purchase cost -/
  c : ℝ
  /-- unit holding cost per period -/
  h : ℝ
  /-- unit backorder cost per period -/
  b : ℝ
  /-- discount factor -/
  α : ℝ
  /-- demand density on `(0, ∞)` -/
  g : ℝ → ℝ
  c_nonneg : 0 ≤ c
  h_pos : 0 < h
  α_pos : 0 < α
  α_lt_one : α < 1
  /-- "To make the problem interesting, we assume that b > ((1 − α)/α) c" (p. 19). -/
  b_gt : (1 - α) / α * c < b
  g_pos : ∀ x : ℝ, 0 < x → 0 < g x
  g_cont : ContinuousOn g (Ioi 0)
  g_total : ∫ x in Ioi (0 : ℝ), g x = 1
  g_mean : IntegrableOn (fun x : ℝ => x * g x) (Ioi 0)

/-- The expected one-period holding and backorder cost `L(y)` of p. 17, when `y` units are
on hand (net) at the beginning of the period and the period's demand has density `g`. -/
noncomputable def Model.L (M : Model) (y : ℝ) : ℝ :=
  if 0 < y then
    M.h * (∫ x in Ioc (0 : ℝ) y, (y - x) * M.g x) + M.b * (∫ x in Ioi y, (x - y) * M.g x)
  else
    M.b * ∫ x in Ioi (0 : ℝ), (x - y) * M.g x

end ServiceParts.BaseStock
