import Mathlib

open MeasureTheory

namespace DRCVRP.Marginal

/-!
The marginalized moment ambiguity sets of Ghosal and Wiesemann, *The Distributionally Robust
Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §4, pp. 723–725. Each is a
set of probability measures on `ℝⁿ = Fin n → ℝ` (joint laws of the demand vector, not products of
marginals). The support `𝒬 = [q̲, q̄]` is the box `Set.Icc qlo qhi`. The standing assumptions
(`q̲ ≥ 0`, `μ ∈ int 𝒬`, convexity, positivity of the bounds) are hypotheses of the theorems.
-/

/-- The marginalized moment ambiguity set (5) (§4, p. 723):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ(q̃ ∈ 𝒬) = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[φ_i(q̃_i)] ≤ σ_i ∀ i ∈ V_C}`, where
`φ_i : ℝ → ℝ^{p_i}` has components `φ i l` and `σ_i ∈ ℝ^{p_i}` has components `σ i l`; the vector
inequality is componentwise. The expectation `𝔼_ℙ[φ_i(q̃_i)]` is required to exist
(integrability); for the closed convex `φ_i` of the paper this is automatic on the bounded
support. -/
def marginalSet {n : ℕ} (qlo qhi μ : Fin n → ℝ) {p : Fin n → ℕ}
    (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ) :
    Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧
    ∀ i l, Integrable (fun q : Fin n → ℝ => φ i l (q i)) P ∧ ∫ q, φ i l (q i) ∂P ≤ σ i l}

/-- The marginalized first-order ambiguity set (6) (§4.1, p. 724):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ(q̃ ∈ 𝒬) = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[|q̃ - μ|] ≤ σ}`, the absolute value and the
inequality taken componentwise: `σ_i` bounds the mean absolute deviation of `q̃_i`. -/
def firstOrderSet {n : ℕ} (qlo qhi μ σ : Fin n → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧ ∀ i, ∫ q, |q i - μ i| ∂P ≤ σ i}

/-- The marginalized variance ambiguity set (8) (§4.2, pp. 724–725):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[(q̃_i - μ_i)²] ≤ σ_i ∀ i ∈ V_C}`:
`σ_i` bounds the variance of `q̃_i`. -/
def varianceSet {n : ℕ} (qlo qhi μ σ : Fin n → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧ ∀ i, ∫ q, (q i - μ i) ^ 2 ∂P ≤ σ i}

/-- The marginalized semivariance ambiguity set (10) (§4.3, p. 725):
`𝒫 = {ℙ ∈ 𝒫₀(ℝⁿ) : ℙ[q̃ ∈ 𝒬] = 1, 𝔼_ℙ[q̃] = μ, 𝔼_ℙ[[q̃_i - μ_i]₊²] ≤ σ_i⁺,
𝔼_ℙ[[μ_i - q̃_i]₊²] ≤ σ_i⁻ ∀ i ∈ V_C}` with `[x]₊ = max x 0`: `σ⁺` and `σ⁻` bound the upper and
the lower semivariance. -/
def semivarianceSet {n : ℕ} (qlo qhi μ σplus σminus : Fin n → ℝ) :
    Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, ∫ q, q i ∂P = μ i) ∧
    (∀ i, ∫ q, (max (q i - μ i) 0) ^ 2 ∂P ≤ σplus i) ∧
    ∀ i, ∫ q, (max (μ i - q i) 0) ^ 2 ∂P ≤ σminus i}

end DRCVRP.Marginal
