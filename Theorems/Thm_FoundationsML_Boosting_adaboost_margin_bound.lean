import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Boosting_AdaBoostNormalizedEnsemble
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace FoundationsML.Boosting

/-- Theorem 7.7 (AdaBoost margin bound; Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 159, PDF p. 176 — this mission's goal). Let
`f = ∑_{t=1}^T α_t h_t` be the function returned by AdaBoost after `T` rounds of boosting, and
assume for all `t ∈ [T]` that `ε_t < 1/2` (which implies `α_t > 0`). Then, for any `ρ > 0`,
`R̂_{S,ρ}(f̄) ≤ 2^T ∏_{t=1}^T sqrt(ε_t^{1−ρ} (1−ε_t)^{1+ρ})`, where `f̄ = f / ∑_t α_t`.

**Formalization Note.** `ε_t^{1-ρ}` and `(1-ε_t)^{1+ρ}` use `Real.rpow` (the `ℝ`-exponent
power, notation `^`, since `ρ : ℝ`), matching the book's real-exponent expression exactly.
`hweak : ∀ t < T, 0 < AdaBoostEpsilon S y h t ∧ AdaBoostEpsilon S y h t < 1/2` is the
weak-learning hypothesis; per `BRIEF.md`'s pitfall note, `α_t > 0` is *not* stated as a separate
free hypothesis, since it is a consequence of `hweak` via `AdaBoostAlpha`'s definition (not
re-derived here, since only the theorem's statement is drafted). The `0 < ε_t` half of `hweak`
excludes the degenerate case `ε_t = 0`, where `AdaBoostAlpha`'s `Real.log`-of-a-zero-division
convention would silently zero out `α_t` instead of the book's intended `+∞`; the book's own
sentence, "assume for all `t∈[T]` that `ε_t < 1/2`, which implies `α_t > 0`," already
presupposes `ε_t` is a well-defined real number for the comparison `α_t > 0` to make sense —
which requires `ε_t ≠ 0` in the first place — so `0 < ε_t < 1/2` is arguably a more literal
reading of the book's own sentence, not merely a defensive addition. `AdaBoostNormalizedEnsemble`
is `f̄` (the normalized combination), matching the book's use of `f̄`, not the raw `f`, in this
statement. -/
theorem adaboost_margin_bound {X : Type*} {m : ℕ} (hm : 0 < m)
    (S : Fin m → X) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (T : ℕ) (h : ℕ → X → ℝ) (hh : ∀ t < T, ∀ x, h t x = 1 ∨ h t x = -1)
    (hweak : ∀ t < T, 0 < AdaBoostEpsilon S y h t ∧ AdaBoostEpsilon S y h t < 1 / 2)
    (ρ : ℝ) (hρ : 0 < ρ) :
    EmpiricalMarginLoss ρ S y (AdaBoostNormalizedEnsemble S y h T) ≤
      2 ^ T * ∏ t ∈ Finset.range T,
        Real.sqrt ((AdaBoostEpsilon S y h t) ^ (1 - ρ) *
          (1 - AdaBoostEpsilon S y h t) ^ (1 + ρ)) := by sorry

end FoundationsML.Boosting
