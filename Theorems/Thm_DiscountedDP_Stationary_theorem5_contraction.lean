import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 5, p. 232. The abstract operator acts on
bounded Borel functions; its two properties are monotonicity and constant shifts. -/
theorem theorem5_contraction
    {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (V : (S → ℝ) → S → ℝ)
    (hmap : ∀ u, IsBM u → IsBM (V u))
    (hmono : ∀ u v, IsBM u → IsBM v →
      (∀ s, u s ≤ v s) → ∀ s, V u s ≤ V v s)
    (hshift : ∀ u, IsBM u → ∀ c : ℝ, ∀ s,
      V (fun t => u t + c) s = V u s + β * c) :
    (∀ u v, IsBM u → IsBM v →
      supNorm (fun s => V u s - V v s) ≤
        β * supNorm (fun s => u s - v s)) ∧
    ∃ ustar : S → ℝ, IsBM ustar ∧ (∀ s, V ustar s = ustar s) ∧
      (∀ v, IsBM v → (∀ s, V v s = v s) → v = ustar) ∧
      ∀ u, IsBM u → ∀ n : ℕ,
        supNorm (fun s => (V^[n] u) s - ustar s) ≤
          β ^ n * supNorm (fun s => u s - ustar s) := by sorry

end DiscountedDP.Stationary

