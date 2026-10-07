import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (3.6) Proposition, p. 107: under condition (1.1)
(`|X_n| ≤ 1` and `E{X_n | ℱ_{n−1}} = 0` for `n ≥ 1`), `E{R_λ(T_σ, S_σ)} ≥ 1` for any `λ ≥ 0`
and any uniformly bounded stopping time `σ`. -/
theorem proposition_3_6 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (hσ_bdd : ∃ N : ℕ, ∀ ω, σ ω ≤ N)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    1 ≤ ∫ ω, R lam (FreedmanTail.Bernstein.T ℱ X P ((σ ω).untopD 0) ω) (FreedmanTail.Bernstein.S X ((σ ω).untopD 0) ω) ∂P := by sorry

end FreedmanTail.Laplace

