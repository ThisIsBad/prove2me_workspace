import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting

namespace SinglePointPricing.Det

noncomputable section

open MeasureTheory

/-- (3.1), p. 13: the truncated generalized Pareto ccdf `Ḡ_{α,t}(v | (s, q_s), (s′, q_{s′}))`:
`Γ_α(Γ_α^{−1}(q_s) v/s)` on `[0, s)`, `q_s Γ_α(Γ_α^{−1}(q_{s′}/q_s) (v − s)/(s′ − s))` on `[s, t]`,
and `0` for `v > t`. -/
def Gbar (α t s qs s' qs' v : ℝ) : ℝ :=
  if v < s then GammaA α (GammaAInv α qs * v / s)
  else if v ≤ t then qs * GammaA α (GammaAInv α (qs' / qs) * (v - s) / (s' - s))
  else 0

/-- (3.2), p. 14: `F̄_α(v | r, (w, q))`, equal to `Ḡ_{α,w}(v | (r, 1), (w, q))` if `r ∈ [0, w)` and
to `Ḡ_{α,r}(v | (0, 1), (w, q))` if `r ≥ w`. -/
def Fbar (α w q r v : ℝ) : ℝ :=
  if r < w then Gbar α w r 1 w q v else Gbar α r 0 1 w q v

/-- (3.3), p. 14: `r̲_α(w, q) = w / (Γ_α^{−1}(q) + 1)`. -/
def rLow (α w q : ℝ) : ℝ := w / (GammaAInv α q + 1)

/-- (3.3)–(3.4), p. 14: the parameter set `[r̲_α(w, q), w) ∪ [w, r̄_α(w, q)]` of `S_{α,w,q}`, with
`r̄_α(w, q) = w / (α Γ_α^{−1}(q))` (`= +∞` for `α = 0`) and `[w, r̄_α] := ∅` when `r̄_α < w`. The
condition `r ≤ r̄_α(w, q)` is written multiplied out, `α Γ_α^{−1}(q) r ≤ w`, which is the same for
`q ∈ (0, 1)` (where `Γ_α^{−1}(q) > 0`) and reads `r < +∞` at `α = 0`. -/
def rSet (α w q : ℝ) : Set ℝ :=
  Set.Ico (rLow α w q) w ∪ {r | w ≤ r ∧ α * GammaAInv α q * r ≤ w}

/-- (3.4), p. 14: `S_{α,w,q} = {F_α(·|r, (w, q)) : r ∈ [r̲_α(w, q), w) ∪ [w, r̄_α(w, q)]}`, as the
value laws on `[0, ∞)` whose closed-tail ccdf is `F̄_α(·|r, (w, q))` for such an `r`. -/
def SFamily (α w q : ℝ) : Set (Measure ℝ) :=
  {μ | IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
    ∃ r ∈ rSet α w q, ∀ v : ℝ, 0 ≤ v → sf μ v = Fbar α w q r v}

/-- (2.1) for a law given by its ccdf `H` on `[0, ∞)`: `opt = sup_{v ≥ 0} v H(v)`. -/
def optFun (H : ℝ → ℝ) : ℝ := sSup ((fun v : ℝ => v * H v) '' Set.Ici 0)

/-- (D-1), p. App-11: `ṽ_α = 1` if `α = 0`, `α^{α/(1−α)}` if `α ∈ (0, 1)`, `e^{−1}` if `α = 1`. -/
def vTilde (α : ℝ) : ℝ :=
  if α = 0 then 1 else if α = 1 then Real.exp (-1) else α ^ (α / (1 - α))

/-- (D-2), p. App-11: `q̲_α = 0` if `α = 0` and `Γ_α(1/α)` if `α ∈ (0, 1]`. -/
def qLow (α : ℝ) : ℝ := if α = 0 then 0 else GammaA α (1 / α)

/-- Proposition D-1, p. App-12: `Δ_{α,q}(p) = (αΓ_α^{−1}(q)(1 − p))² + 4Γ_α^{−1}(q)(1 − p)q^{α−1}`. -/
def Delta (α q p : ℝ) : ℝ :=
  (α * GammaAInv α q * (1 - p)) ^ 2 + 4 * GammaAInv α q * (1 - p) * q ^ (α - 1)

/-- Proposition D-1, p. App-12:
`µ_{α,q}(p) = 1 − (√Δ_{α,q}(p) − αΓ_α^{−1}(q)(1 − p)) / (2q^{α−1})`. -/
def muAQ (α q p : ℝ) : ℝ :=
  1 - (Real.sqrt (Delta α q p) - α * GammaAInv α q * (1 - p)) / (2 * q ^ (α - 1))

/-- p. App-12: `R_{1,α}(p, q) = Rev(p|F̄_α(·|µ_{α,q}(p), (1, q))) / opt(F_α(·|µ_{α,q}(p), (1, q)))`
(normalized initial price `w = 1`). -/
def R1 (α q p : ℝ) : ℝ :=
  p * Fbar α 1 q (muAQ α q p) p / optFun (Fbar α 1 q (muAQ α q p))

/-- p. App-12: `R_{2,α}(p, q) = Rev(p|δ_1) / Rev(1|δ_1)` (independent of `α` and `q`). -/
def R2 (p : ℝ) : ℝ :=
  p * sf (Measure.dirac 1) p / (1 * sf (Measure.dirac 1) 1)

/-- p. App-12: `R_{3,α}(p, q) = Rev(p|F̄_α(·|r̄_α(1, q), (1, q))) / opt(F_α(·|r̄_α(1, q), (1, q)))`
with `r̄_α(1, q) = 1/(αΓ_α^{−1}(q))` (used for `q ≥ q̲_α`). For `α = 0`, `r̄_0 = +∞` and the law is
the untruncated tail `Γ_0(Γ_0^{−1}(q) v)`, whose `opt` is the limit `ṽ_0 / Γ_0^{−1}(q)` (p. App-17);
the ratio is then `(Γ_0^{−1}(q)/ṽ_0) p Γ_0(Γ_0^{−1}(q) p)`. -/
def R3 (α q p : ℝ) : ℝ :=
  if α = 0 then (GammaAInv 0 q / vTilde 0) * (p * GammaA 0 (GammaAInv 0 q * p))
  else p * Fbar α 1 q (1 / (α * GammaAInv α q)) p /
    optFun (Fbar α 1 q (1 / (α * GammaAInv α q)))

end

end SinglePointPricing.Det
