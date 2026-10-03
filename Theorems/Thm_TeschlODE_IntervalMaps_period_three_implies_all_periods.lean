import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.1, p. 294: let `I = [a, b] ⊆ ℝ` be a compact interval and `f : I → I`
continuous. If `f` has an orbit of (prime) period three, then for every `n ∈ ℕ = {1, 2, …}` it
has an orbit of prime period `n`. The prime period is Mathlib's `Function.minimalPeriod`. -/
theorem period_three_implies_all_periods (a b : ℝ) (hab : a ≤ b)
    (f : Set.Icc a b → Set.Icc a b) (hf : Continuous f)
    (h3 : ∃ x : Set.Icc a b, Function.minimalPeriod f x = 3) :
    ∀ n : ℕ, 1 ≤ n → ∃ x : Set.Icc a b, Function.minimalPeriod f x = n := by sorry

end TeschlODE.IntervalMaps

