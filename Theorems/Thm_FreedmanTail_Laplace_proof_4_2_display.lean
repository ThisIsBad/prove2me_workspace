import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums
import Definitions.Def_FreedmanTail_Laplace_CrossingTime

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (4.2), p. 108, the display: under condition (1.1), with `a > 0` and
`λ > 0`, for every `n`, writing `k = τ_a ∧ n`,
`1 ≤ E{exp[λS_k − f(λ)T_k]} ≤ exp[λ(a + 1)] · E{exp[−f(λ)T_k]}`.
(The page omits the `E` of the last factor.) -/
theorem proof_4_2_display {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    1 ≤ ∫ ω, R lam (FreedmanTail.Bernstein.T ℱ X P ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω)
        (FreedmanTail.Bernstein.S X ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω) ∂P ∧
    ∫ ω, R lam (FreedmanTail.Bernstein.T ℱ X P ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω)
        (FreedmanTail.Bernstein.S X ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω) ∂P ≤
      Real.exp (lam * (a + 1)) *
        ∫ ω, Real.exp (-(f lam * FreedmanTail.Bernstein.T ℱ X P ((min (tau a X ω) (n : WithTop ℕ)).untopD 0) ω)) ∂P := by sorry

end FreedmanTail.Laplace

