import Mathlib

namespace DemandResponse.FirstBest

/-- The parameters of the demand-response model of Aïd, Possamaï and Touzi (arXiv:1810.09063v3,
§2.1–2.2, pp. 7–9, and (3.1), p. 10), with every standing hypothesis of the paper as a field.

* `N`, `d` : numbers of usages for the mean effort and for the volatility effort;
* `μ i`, `lam j` : cost parameters, `σ j` : nominal volatilities, all positive;
* `Amax`, `ε` : effort bounds, `A = Π i [0, μ i Amax]`, `B = [ε, 1]^d`;
* `r`, `p` : CARA coefficients of the consumer and of the producer;
* `h` : marginal cost of volatility;
* `κ`, `θ` : `f(x) = κ x` (value of consumption) and `g(x) = θ x` (generation cost);
* `T` : horizon, `X₀` : initial consumption, `R₀` : reservation utility.

Added (disclosed): `ε ≤ 1` (so that `B` is nonempty) and `R₀ < 0` (the page writes
`R₀ ∈ ℝ₋`; `L₀ = -(1/r) log(-R₀)` needs `-R₀ > 0`). -/
structure Params (N d : ℕ) where
  μ : Fin N → ℝ
  lam : Fin d → ℝ
  σ : Fin d → ℝ
  Amax : ℝ
  ε : ℝ
  r : ℝ
  p : ℝ
  h : ℝ
  κ : ℝ
  θ : ℝ
  T : ℝ
  X₀ : ℝ
  R₀ : ℝ
  hμ : ∀ i, 0 < μ i
  hlam : ∀ j, 0 < lam j
  hσ : ∀ j, 0 < σ j
  hAmax : 0 < Amax
  hε : 0 < ε
  hε1 : ε ≤ 1
  hr : 0 < r
  hp : 0 < p
  hh : 0 < h
  hT : 0 < T
  hR₀ : R₀ < 0

variable {N d : ℕ}

/-- The negative part `x⁻ := 0 ∨ (-x)` (p. 9). -/
def xneg (x : ℝ) : ℝ := max 0 (-x)

/-- `μ̄ := μ · 1 = Σ i μ i`. -/
def muBar (P : Params N d) : ℝ := ∑ i, P.μ i

/-- Energy value discrepancy `δ := κ - θ`, so that `(f - g)(x) = δ x` (3.1). -/
def delta (P : Params N d) : ℝ := P.κ - P.θ

/-- `ρ := r p / (r + p)`, i.e. `1/ρ = 1/r + 1/p` (p. 26). -/
noncomputable def rho (P : Params N d) : ℝ := P.r * P.p / (P.r + P.p)

/-- Certainty equivalent of the reservation utility, `L₀ := -(1/r) log(-R₀)` (p. 8). -/
noncomputable def L0 (P : Params N d) : ℝ := -(1 / P.r) * Real.log (-P.R₀)

/-- The producer's utility `U(x) := -e^{-p x}` (2.4). -/
noncomputable def U (P : Params N d) (x : ℝ) : ℝ := -Real.exp (-P.p * x)

/-- The mean-effort box `A := [0, μ₁ Amax] × ⋯ × [0, μ_N Amax]` (p. 8). -/
def effortA (P : Params N d) : Set (Fin N → ℝ) :=
  {a | ∀ i, 0 ≤ a i ∧ a i ≤ P.μ i * P.Amax}

/-- The volatility-effort box `B := [ε, 1]^d` (p. 8). -/
def effortB (P : Params N d) : Set (Fin d → ℝ) :=
  {b | ∀ j, P.ε ≤ b j ∧ b j ≤ 1}

/-- `c₁(a) := ½ Σ i a_i² / μ_i` (p. 8). -/
noncomputable def c1 (P : Params N d) (a : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ i, a i ^ 2 / P.μ i

/-- `c₂(b) := Σ j (σ_j² / λ_j) (b_j⁻¹ - 1)` (p. 8). -/
noncomputable def c2 (P : Params N d) (b : Fin d → ℝ) : ℝ :=
  ∑ j, P.σ j ^ 2 / P.lam j * ((b j)⁻¹ - 1)

/-- The effort cost `c(a, b) := c₁(a) + ½ c₂(b)` (p. 8). -/
noncomputable def cost (P : Params N d) (a : Fin N → ℝ) (b : Fin d → ℝ) : ℝ :=
  c1 P a + (1 / 2) * c2 P b

/-- `|σ(b)|² = Σ j σ_j² b_j`, where `σ(b) := (σ₁ √b₁, …, σ_d √b_d)` (2.1). -/
def sigSq (P : Params N d) (b : Fin d → ℝ) : ℝ := ∑ j, P.σ j ^ 2 * b j

/-- `H_m(z) := - inf_{a ∈ A} { a · 1 z + c₁(a) }` (2.9). The infimum is the real `sInf` of the
image of the nonempty compact box `A` under a continuous map, so it is attained. -/
noncomputable def Hm (P : Params N d) (z : ℝ) : ℝ :=
  -sInf ((fun a => (∑ i, a i) * z + c1 P a) '' effortA P)

/-- `H_v(γ) := -½ inf_{b ∈ B} { c₂(b) - γ |σ(b)|² }` (2.9). The infimum is the real `sInf` of
the image of the nonempty compact box `B ⊆ (0, ∞)^d` under a continuous map, so it is
attained. -/
noncomputable def Hv (P : Params N d) (γ : ℝ) : ℝ :=
  -(1 / 2) * sInf ((fun b => c2 P b - γ * sigSq P b) '' effortB P)

/-- The consumer's best response on the drift, `â_i(z) := μ_i (z⁻ ∧ Amax)` (Prop. 2.1). -/
def aHat (P : Params N d) (z : ℝ) : Fin N → ℝ :=
  fun i => P.μ i * min (xneg z) P.Amax

/-- The consumer's best response on the volatilities, `b̂_j(γ) := (1 ∧ (λ_j γ⁻)^{-1/2}) ∨ ε`
(Prop. 2.1, with `j = 1, …, d`). For `λ_j γ⁻ ≤ 1`, in particular for `γ⁻ = 0` where the paper
reads `(λ_j γ⁻)^{-1/2} = +∞`, the minimum with `1` is `1`; the case split avoids Lean's
`0 ^ (-1/2) = 0`. -/
noncomputable def bHat (P : Params N d) (γ : ℝ) : Fin d → ℝ :=
  fun j => if P.lam j * xneg γ ≤ 1 then 1 else max P.ε ((P.lam j * xneg γ) ^ (-(1 / 2 : ℝ)))

end DemandResponse.FirstBest
