import Mathlib

namespace MDPFinance.TerminalWealth

/-- The binomial-model one-period power-utility objective (Bäuerle–Rieder, p. 86, PDF 100,
unnumbered display, constant `(1+i)^{-γ}` dropped): `h(α) := p(1+i+α(u-1-i))^γ +
(1-p)(1+i+α(d-1-i))^γ`. -/
noncomputable def binomialObjective (i u down γ p α : ℝ) : ℝ :=
  p * (1 + i + α * (u - 1 - i)) ^ γ + (1 - p) * (1 + i + α * (down - 1 - i)) ^ γ

/-- The optimal fraction invested in the stock in the binomial model, Eq. (4.9) (Bäuerle–Rieder,
p. 86, PDF 100), with `δ := (1-γ)⁻¹`. -/
noncomputable def binomialAlphaStar (i u down γ p : ℝ) : ℝ :=
  let δ := (1 - γ)⁻¹
  (1 + i) / ((1 + i - down) * (u - 1 - i)) *
    (((u - 1 - i) ^ δ * p ^ δ - (1 + i - down) ^ δ * (1 - p) ^ δ) /
      ((u - 1 - i) ^ (δ * γ) * p ^ δ + (1 + i - down) ^ (δ * γ) * (1 - p) ^ δ))

/-- The endpoints of the admissible interval `[α_0,α_1]` for the binomial one-period problem
(Bäuerle–Rieder, p. 86, PDF 100). -/
noncomputable def binomialAlpha0 (i u : ℝ) : ℝ := (1 + i) / (1 + i - u)

noncomputable def binomialAlpha1 (i down : ℝ) : ℝ := (1 + i) / (1 + i - down)

end MDPFinance.TerminalWealth
