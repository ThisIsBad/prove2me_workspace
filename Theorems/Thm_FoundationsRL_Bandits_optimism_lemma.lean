import Mathlib

namespace FoundationsRL.Bandits

/-- Lemma 7 (Optimism), Foster–Rakhlin p. 28. Fix a round with confidence bounds
`fLo ≤ fStar ≤ fHi` valid for every decision. Then the optimistic action `pit`
(the maximizer of `fHi`) has instantaneous regret at most the confidence width
at `pit`: `fStar piStar - fStar pit ≤ fHi pit - fLo pit`. -/
theorem optimism_lemma {A : ℕ} (fStar : Fin A → ℝ) (piStar : Fin A)
    (hStar : ∀ a : Fin A, fStar a ≤ fStar piStar)
    (fLo fHi : Fin A → ℝ) (hCI : ∀ a : Fin A, fStar a ∈ Set.Icc (fLo a) (fHi a))
    (pit : Fin A) (hOpt : ∀ a : Fin A, fHi a ≤ fHi pit) :
    fStar piStar - fStar pit ≤ fHi pit - fLo pit := by sorry

end FoundationsRL.Bandits

