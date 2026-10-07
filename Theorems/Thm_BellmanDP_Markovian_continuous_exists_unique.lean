import Mathlib
import Definitions.Def_BellmanDP_Markovian_Continuous

namespace BellmanDP.Markovian

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 1, p. 321. Let row `i`'s parameter range
over `S i`, with `‖A(q, t)‖, ‖b(q, t)‖ ≤ f(t)` for every admissible joint `q` and `t ≥ 0` (norms
(3.5): sums of absolute values), `f` integrable over every `[0, T]`, and let
`F(t, x) = Max_q [A(q, t) x + b(q, t)]` (row by row, maximum attained). Assume `t ↦ F(t, x)` is
measurable for each `x`. Then `dx/dt = F(t, x)`, `x(0) = c`, has a solution satisfying the
equation almost everywhere (in integral form) on every `[0, T]`; any solution on an interval
`[0, S']` coincides with it there; and the successive approximations (5.3) converge to it
uniformly on every `[0, T]`. -/
theorem continuous_exists_unique {N : ℕ} {Q : Fin N → Type*}
    (A : (i : Fin N) → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → Q i → ℝ → ℝ)
    (S : (i : Fin N) → Set (Q i)) (f : ℝ → ℝ)
    (hf : ∀ T : ℝ, IntegrableOn f (Set.Icc 0 T))
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, ∑ j, |A i (q i) t j| ≤ f t)
    (hb : ∀ t : ℝ, 0 ≤ t → ∀ q ∈ Set.pi Set.univ S, ∑ i, |b i (q i) t| ≤ f t)
    (F : ℝ → (Fin N → ℝ) → Fin N → ℝ) (hF : IsRowwiseMax A b S F)
    (hFmeas : ∀ x : Fin N → ℝ, Measurable fun t => F t x) (c : Fin N → ℝ) :
    ∃ x : ℝ → Fin N → ℝ,
      (∀ T : ℝ, 0 < T → IsIntegralSolutionOn F c T x) ∧
      (∀ S' : ℝ, 0 < S' → ∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn F c S' z →
        Set.EqOn z x (Set.Icc 0 S')) ∧
      (∀ T : ℝ, 0 < T → TendstoUniformlyOn (picardIter F c) x Filter.atTop (Set.Icc 0 T)) := by sorry

end BellmanDP.Markovian

