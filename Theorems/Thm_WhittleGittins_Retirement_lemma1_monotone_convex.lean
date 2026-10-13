import Mathlib
import Definitions.Def_WhittleGittins_Retirement_BanditProcess

namespace WhittleGittins.Retirement

open MeasureTheory ProbabilityTheory

/-- Lemma 1 (p. 144): `F(x, M)` is non-decreasing and convex in `M`, equals `Φ(x)` for `M ≤ k` and
`M` for `M ≥ K`; for `M < k` retirement is never optimal and the one-step values `Lᵢ F` and
`Lᵢ Φ` coincide, so the optimal policies of the two processes are identical. -/
theorem lemma1_monotone_convex {N : ℕ} [NeZero N] {X : Fin N → Type*}
    [∀ i, MeasurableSpace (X i)] (B : BanditProcess N X)
    (F : (∀ j, X j) → ℝ → ℝ) (Φ : (∀ j, X j) → ℝ)
    (hF : IsMProcessValue B F) (hΦ : IsContinuingValue B Φ) (x : ∀ j, X j) :
    Monotone (F x) ∧ ConvexOn ℝ Set.univ (F x) ∧
      (∀ M, M ≤ B.k → F x M = Φ x) ∧ (∀ M, B.K ≤ M → F x M = M) ∧
      (∀ M, M < B.k → M < F x M ∧ ∀ i, Lop B i (fun z => F z M) x = Lop B i Φ x) := by sorry

end WhittleGittins.Retirement

