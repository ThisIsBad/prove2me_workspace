import Mathlib

namespace SinglePointPricing.Det

noncomputable section

open MeasureTheory

/-- §2, p. 9: the complementary cumulative distribution function `F̄(p) = P(v ≥ p)` of a value law
`μ` on `ℝ`, taken as the **closed** tail `μ([p, ∞))` (p. 2: "values … greater than or equal to w";
p. 9: `Rev(p|F̄) = ∫ p 1{v ≥ p} dF(v) = p F̄(p)`). -/
def sf (μ : Measure ℝ) (p : ℝ) : ℝ := (μ (Set.Ici p)).toReal

/-- (2.2), p. 10: the class `G` of value laws: probability measures supported in `[0, ∞)` with
finite and non-zero expectation (the data constraint `F̄(w) ∈ I` is added in `FClass`). -/
def InG (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ Integrable (fun v : ℝ => v) μ ∧ 0 < ∫ v, v ∂μ

/-- (2.1), p. 9: the oracle revenue `opt(F) = sup_{p ≥ 0} p F̄(p)`. -/
def opt (μ : Measure ℝ) : ℝ := sSup ((fun p : ℝ => p * sf μ p) '' Set.Ici 0)

/-- p. 13: `Γ_α(v) = (1 + (1 − α) v)^{−1/(1−α)}` for `α ∈ [0, 1)` and `e^{−v}` for `α = 1`. -/
def GammaA (α v : ℝ) : ℝ :=
  if α = 1 then Real.exp (-v) else (1 + (1 - α) * v) ^ (-(1 / (1 - α)))

/-- p. 13: the inverse `Γ_α^{−1}` of `Γ_α`, on `(0, 1]`: `(q^{−(1−α)} − 1)/(1 − α)` for `α ∈ [0, 1)`
and `−log q` for `α = 1`. (Only used at arguments in `(0, 1]`; the paper's `Γ_α^{−1}(0) = +∞` never
arises.) -/
def GammaAInv (α q : ℝ) : ℝ :=
  if α = 1 then -Real.log q else (q ^ (-(1 - α)) - 1) / (1 - α)

/-- p. 11 and App. A, p. App-1: `α`-strong regularity, stated as convexity of `Γ_α^{−1} ∘ F̄` on
`{v ≥ 0 | F̄(v) > 0}`. This is equivalent to the paper's density form (positive density on the
support except possibly an atom at its maximum, `(1 − α)v − F̄(v)/f(v)` non-decreasing); no absolute
continuity is required, so an atom at the top of the support is allowed, as on p. 11. -/
def IsAlphaSR (α : ℝ) (μ : Measure ℝ) : Prop :=
  ConvexOn ℝ {v : ℝ | 0 ≤ v ∧ 0 < sf μ v} (fun v => GammaAInv α (sf μ v))

/-- p. 11: `F_α(w, q) = {F ∈ G(w, {q}) : F is α-strongly regular}`, the α-strongly regular value
laws with conversion rate `F̄(w) = q` at the price `w`. -/
def FClass (α w q : ℝ) : Set (Measure ℝ) :=
  {μ | InG μ ∧ IsAlphaSR α μ ∧ sf μ w = q}

/-- p. 9: the class `P` of (randomized) pricing mechanisms: laws of posted prices on `[0, ∞)`. -/
def IsMech (Ψ : Measure ℝ) : Prop :=
  IsProbabilityMeasure Ψ ∧ Ψ (Set.Iio 0) = 0

/-- p. 10: the deterministic mechanisms `P_d = {δ_γ : γ ≥ 0}`. -/
def Pd : Set (Measure ℝ) := {Ψ | ∃ γ : ℝ, 0 ≤ γ ∧ Ψ = Measure.dirac γ}

/-- p. 9: the performance `R(Ψ, F) = ∫ Rev(p|F̄) dΨ(p) / opt(F)` of the mechanism `Ψ` against `F`. -/
def ratio (Ψ μ : Measure ℝ) : ℝ := (∫ p, p * sf μ p ∂Ψ) / opt μ

/-- p. 10: the maximin ratio `R(P′, 𝓕) = sup_{Ψ ∈ P′} inf_{F ∈ 𝓕} R(Ψ, F)`. -/
def maximin (P' 𝓕 : Set (Measure ℝ)) : ℝ :=
  sSup ((fun Ψ => sInf (ratio Ψ '' 𝓕)) '' P')

/-- p. 22: the Lambert function `W`, the inverse of `x ↦ x e^x` on `[0, +∞)`: for `x ≥ 0`,
`lambertW x` is the unique `w ≥ 0` with `w e^w = x` (junk value `0` for `x < 0`). -/
def lambertW (x : ℝ) : ℝ :=
  open Classical in
  if h : ∃ w : ℝ, 0 ≤ w ∧ w * Real.exp w = x then Classical.choose h else 0

/-- p. 22: `β_q(x) = 1 − (1/log(q^{−1})) (W(x) + 1/W(x) − 2)`. -/
def betaQ (q x : ℝ) : ℝ :=
  1 - (lambertW x + 1 / lambertW x - 2) / Real.log q⁻¹

/-- p. 22: `ρ(q) = β_q(1/log(q^{−1})) e log(q^{−1}) e^{−log(q^{−1}) β_q(1/log(q^{−1}))}`. -/
def rhoQ (q : ℝ) : ℝ :=
  betaQ q (1 / Real.log q⁻¹) * Real.exp 1 * Real.log q⁻¹ *
    Real.exp (-(Real.log q⁻¹) * betaQ q (1 / Real.log q⁻¹))

end

end SinglePointPricing.Det
