import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (3.3) Proposition, p. 106: under (3.4), for `λ ≥ 0` and any stopping
time `σ` (the value `∞ = ⊤` allowed), `∫_{σ<∞} Q_λ(T_σ, S_σ) dP ≤ 1`. -/
theorem proposition_3_3 {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 ≤ lam) (σ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) :
    ∫⁻ ω in {ω | σ ω ≠ ⊤},
        ENNReal.ofReal (stoppedValue (fun n ω => Q lam (T ℱ X P n ω) (S X n ω)) σ ω) ∂P ≤ 1 := by sorry

end FreedmanTail.Bernstein

