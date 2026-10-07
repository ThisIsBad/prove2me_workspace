import Mathlib
import Definitions.Def_BellmanDP_Markovian_Continuous

namespace BellmanDP.Markovian

open MeasureTheory

/-- Bellman, *Dynamic Programming*, Ch. XI, Theorem 4, p. 332. Let row `i`'s players choose
`p ∈ SP i`, `q ∈ SQ i`, and let `V(t, x)` be, row by row, the common value
`Max_p Min_q [A(p, q, t) x + b(p, q, t)] = Min_q Max_p […]` (condition (2a)). Assume (2b):
`Max_S ‖A(p, q, t)‖, Max_S ‖b(p, q, t)‖ ≤ f(t)` for `t ≥ 0` with `∫_0^T f(t) dt < ∞`, and that
`t ↦ V(t, x)` is measurable for each `x`. Then `dx/dt = V(t, x)`, `x(0) = c`, has a unique
solution on `0 ≤ t ≤ T` satisfying the equation almost everywhere (in integral form), and it is
the uniform limit on `[0, T]` of the successive approximations (12.3). -/
theorem minmax_exists_unique {N : ℕ} {P Q : Fin N → Type*}
    (A : (i : Fin N) → P i → Q i → ℝ → Fin N → ℝ) (b : (i : Fin N) → P i → Q i → ℝ → ℝ)
    (SP : (i : Fin N) → Set (P i)) (SQ : (i : Fin N) → Set (Q i))
    (V : ℝ → (Fin N → ℝ) → Fin N → ℝ) (hV : IsRowwiseSaddleValue A b SP SQ V)
    (hVmeas : ∀ x : Fin N → ℝ, Measurable fun t => V t x)
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc 0 T))
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ p ∈ Set.pi Set.univ SP, ∀ q ∈ Set.pi Set.univ SQ,
      ∑ i, ∑ j, |A i (p i) (q i) t j| ≤ f t)
    (hb : ∀ t : ℝ, 0 ≤ t → ∀ p ∈ Set.pi Set.univ SP, ∀ q ∈ Set.pi Set.univ SQ,
      ∑ i, |b i (p i) (q i) t| ≤ f t)
    (c : Fin N → ℝ) :
    ∃ x : ℝ → Fin N → ℝ, IsIntegralSolutionOn V c T x ∧
      (∀ z : ℝ → Fin N → ℝ, IsIntegralSolutionOn V c T z → Set.EqOn z x (Set.Icc 0 T)) ∧
      TendstoUniformlyOn (picardIter V c) x Filter.atTop (Set.Icc 0 T) := by sorry

end BellmanDP.Markovian

