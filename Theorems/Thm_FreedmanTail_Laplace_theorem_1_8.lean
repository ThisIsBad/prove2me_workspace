import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums
import Definitions.Def_FreedmanTail_Laplace_CrossingTime

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (1.8) Theorem, p. 102 (proved in (4.2), p. 108): under condition (1.1)
(`|X_n| ≤ 1` and `E{X_n | ℱ_{n−1}} = 0` for `n ≥ 1`), for `λ > 0` and `a > 0`,
`E{exp[−f(λ)W_a]} ≥ exp[−λ(a + 1)]`, where `W_a = T_{τ_a} ∈ [0, ∞]` is the conditional variance
accumulated up to the first crossing of level `a`, and `exp[−f(λ)·∞] = 0`. -/
theorem theorem_1_8 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (ha : 0 < a) :
    Real.exp (-(lam * (a + 1))) ≤ ∫ ω, expNegMul (f lam) (W a ℱ X P ω) ∂P := by sorry

end FreedmanTail.Laplace

