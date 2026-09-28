import Mathlib

namespace PreorderADI.Correlation

open MeasureTheory ProbabilityTheory

/-- `Φ`, the standard normal distribution function (Li–Zhang 2013, §3, p. 60). -/
noncomputable def stdNormalCdf (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- `φ`, the standard normal density (Li–Zhang 2013, §3, p. 60). -/
noncomputable def stdNormalPdf (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The parameters of the preorder model of §3–§4 (p. 60): valuations `v_H`, `v_L`, unit cost `c`,
discount factor `δ`, mean high-type demand `μ_H`, mean and standard deviation `μ_L`, `σ_L` of
low-type demand, and the critical-fractile quantile `z_L` of p. 61. -/
structure Params where
  vH : ℝ
  vL : ℝ
  c : ℝ
  delta : ℝ
  muH : ℝ
  muL : ℝ
  sigmaL : ℝ
  zL : ℝ

/-- The standing assumptions of §3 (p. 60): `v_H > v_L`, `c < v_L`, `δ ≤ 1`, `δ v_H > v_L`;
the added positivity of `c`, `μ_H`, `μ_L`, `σ_L`; and `z_L = Φ⁻¹((v_L − c)/v_L)` (p. 61),
stated as `Φ(z_L) = (v_L − c)/v_L`. -/
structure Params.Standing (P : Params) : Prop where
  c_pos : 0 < P.c
  c_lt_vL : P.c < P.vL
  vL_lt_vH : P.vL < P.vH
  delta_le_one : P.delta ≤ 1
  vL_lt_delta_vH : P.vL < P.delta * P.vH
  muH_pos : 0 < P.muH
  muL_pos : 0 < P.muL
  sigmaL_pos : 0 < P.sigmaL
  zL_spec : stdNormalCdf P.zL = (P.vL - P.c) / P.vL

/-- `Δ = δ v_H − v_L` (p. 62). -/
def Params.Delta (P : Params) : ℝ := P.delta * P.vH - P.vL

/-- `λ_L = μ_L / σ_L` (p. 60). -/
noncomputable def Params.lamL (P : Params) : ℝ := P.muL / P.sigmaL

/-- `μ̃_L(x) = μ_L + ρ σ_L x`, the mean of the updated low-type demand (p. 60). -/
def lowMean (P : Params) (ρ x : ℝ) : ℝ := P.muL + ρ * P.sigmaL * x

/-- `σ̃_L = σ_L √(1 − ρ²)`, the standard deviation of the updated low-type demand (p. 60). -/
noncomputable def lowSd (P : Params) (ρ : ℝ) : ℝ := P.sigmaL * Real.sqrt (1 - ρ ^ 2)

/-- `Q(x) = μ̃_L(x) + z_L σ̃_L`, the order quantity of (1) (p. 61). -/
noncomputable def orderQty (P : Params) (ρ x : ℝ) : ℝ := lowMean P ρ x + P.zL * lowSd P ρ

/-- The law of the updated low-type demand `X̃_L(x)`: normal with mean `μ̃_L(x)` and
standard deviation `σ̃_L` (p. 60). -/
noncomputable def lowDemandLaw (P : Params) (ρ x : ℝ) : Measure ℝ :=
  gaussianReal (lowMean P ρ x) (Real.toNNReal (lowSd P ρ ^ 2))

/-- The seller's expected second-period profit when ordering `Q` at price `p_2 = v_L`, with zero
salvage value and no shortage penalty: `E[v_L min(Q, X̃_L(x)) − c Q]` (pp. 60–61). -/
noncomputable def expectedSecondProfit (P : Params) (ρ x Q : ℝ) : ℝ :=
  ∫ y, (P.vL * min Q y - P.c * Q) ∂(lowDemandLaw P ρ x)

/-- `Π_L(x) = (v_L − c)(μ_L + ρ σ_L x) − v_L φ(z_L) σ_L √(1 − ρ²)`, display (2) (p. 61). -/
noncomputable def secondProfit (P : Params) (ρ x : ℝ) : ℝ :=
  (P.vL - P.c) * (P.muL + ρ * P.sigmaL * x)
    - P.vL * stdNormalPdf P.zL * P.sigmaL * Real.sqrt (1 - ρ ^ 2)

/-- `ξ = E[Pr(X̃_L(X)/2 < Q(X))]`, the first expression of (3) (p. 61), with `X` standard
normal and the rationing belief `θ = 1/2`. -/
noncomputable def availability (P : Params) (ρ : ℝ) : ℝ :=
  ∫ x, (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x} ∂(gaussianReal 0 1)

/-- `Π^p = (v_H − Δ ξ − c) μ_H + Π_L(0)`, the preorder profit (4) (p. 62), as a function of `ρ`. -/
noncomputable def preorderProfit (P : Params) (ρ : ℝ) : ℝ :=
  (P.vH - P.Delta * availability P ρ - P.c) * P.muH + secondProfit P ρ 0

/-- `μ̃(ρ) = − v_L φ(z_L) σ_L / (2 Δ z_L φ(2 z_L √(1 − ρ²) + λ_L))`, the threshold (6) (p. 62). -/
noncomputable def threshold (P : Params) (ρ : ℝ) : ℝ :=
  -(P.vL * stdNormalPdf P.zL * P.sigmaL) /
    (2 * P.Delta * P.zL * stdNormalPdf (2 * P.zL * Real.sqrt (1 - ρ ^ 2) + P.lamL))

end PreorderADI.Correlation
