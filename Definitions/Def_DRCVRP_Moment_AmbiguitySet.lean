import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional

open MeasureTheory

namespace DRCVRP.Moment

/-- The moment ambiguity set (4) (Ghosal–Wiesemann, §3, p. 722):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ(q̃ ∈ 𝒬) = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[φ(q̃)] ≤ σ}` with the rectangular support
`𝒬 = [qlo, qhi]`, the mean vector `μ`, the dispersion measure `φ : ℝⁿ → ℝᵖ` (component `l` is
`φ l`) and the dispersion bounds `σ`. Customers are `Fin n` (0-based). The integrability clauses
make the expectations genuine Bochner integrals; they hold automatically for a probability measure
carried by the box when each `φ l` is continuous (e.g. convex). -/
def momentAmbiguitySet {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (φ : Fin p → (Fin n → ℝ) → ℝ)
    (σ : Fin p → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, Integrable (fun q => q i) P ∧ ∫ q, q i ∂P = μ i) ∧
    ∀ l, Integrable (φ l) P ∧ ∫ q, φ l q ∂P ≤ σ l}

/-- The worst-case value-at-risk `sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` of the cumulative demand
of the customer subset `S` over an ambiguity set `Amb` (the paper's `𝒫`) (§3, p. 721). -/
noncomputable def worstCaseVaR {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  sSup ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb)

/-- The demand estimator (2) (§3, p. 721):
`d_𝒫(S) = max {⌈(1/Q) sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]⌉, 1}` for `S ≠ ∅`, and
`d_𝒫(∅) = 0`. -/
noncomputable def demandEstimator {n : ℕ} (Amb : Set (Measure (Fin n → ℝ))) (ε Q : ℝ)
    (S : Finset (Fin n)) : ℤ :=
  if S = ∅ then 0 else max ⌈worstCaseVaR Amb ε S / Q⌉ 1

/-- The two-point distribution `p₁ · δ_{q₁} + p₂ · δ_{q₂}` on `ℝⁿ` (§3, p. 723, Proposition 1). -/
noncomputable def twoPointMeasure {n : ℕ} (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ) :
    Measure (Fin n → ℝ) :=
  ENNReal.ofReal p₁ • Measure.dirac q₁ + ENNReal.ofReal p₂ • Measure.dirac q₂

end DRCVRP.Moment
