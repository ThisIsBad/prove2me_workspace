import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.FinancialMarkets

/-- An `N`-period financial market with `d` risky assets and one riskless bond
(Bäuerle–Rieder, p. 61, PDF 75-76): a probability space `(Ω,𝓕,ℙ)` with filtration `(Fam n)`,
`Fam 0` trivial; a deterministic per-period interest rate `i : ℕ → ℝ` (`i (n+1)` the rate on
`[n,n+1)`); and relative price changes `R̃ : ℕ → Ω → Fin d → ℝ` (`R̃ (n+1)` the vector of
relative returns on `[n,n+1)`, `Fam (n+1)`-measurable, a.s. strictly positive, for
`n = 0, …, N-1`); the bond factors `1 + i_n` are positive. -/
structure DiscreteFinancialMarket (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  Fam : ℕ → MeasurableSpace Ω
  hFam_mono : Monotone Fam
  hFam_le : ∀ n, Fam n ≤ ‹MeasurableSpace Ω›
  hFam0_trivial : ∀ s, MeasurableSet[Fam 0] s → s = ∅ ∨ s = Set.univ
  i : ℕ → ℝ
  /-- The bond price `S⁰_{n+1} = S⁰_n (1 + i_{n+1})` stays positive, so that the relative risk
  process `R̃/(1+i) − 1` and the wealth recursion (3.1) are meaningful. -/
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  Rtilde : ℕ → Ω → (Fin d → ℝ)
  hRtilde_adapted : ∀ n, 1 ≤ n → n ≤ N → @Measurable Ω (Fin d → ℝ) (Fam n) _ (Rtilde n)
  hRtilde_pos : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ ω ∂measIP, ∀ k, 0 < Rtilde n ω k

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The relative risk process `R_n^k := R̃_n^k / (1 + i_n) - 1` (Bäuerle–Rieder, p. 63, PDF 77,
unnumbered display) — the excess return of asset `k` over the riskless rate, on `[n-1,n)`. -/
noncomputable def DiscreteFinancialMarket.R (M : DiscreteFinancialMarket Ω d) (n : ℕ) (ω : Ω)
    (k : Fin d) : ℝ :=
  M.Rtilde n ω k / (1 + M.i n) - 1

end MDPFinance.FinancialMarkets
