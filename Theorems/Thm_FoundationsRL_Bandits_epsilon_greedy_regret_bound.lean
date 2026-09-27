import Mathlib
import Definitions.Def_FoundationsRL_Bandits_regret

namespace FoundationsRL.Bandits

/-- Proposition 4 (ε-Greedy regret), Foster–Rakhlin p. 24. Assume `fStar π ∈ [0,1]`
for every decision `π`. Conditional on the estimation event of Eq. (2.9) — that at
every round `t ≤ T` the empirical mean concentrates around `fStar` at the rate the
ε-fraction of uniform exploration buys — and with `ε` set to the value (Eq. (2.14))
that balances the two terms of the regret decomposition, the ε-Greedy algorithm's
regret satisfies `Reg ≲ A^{1/3} T^{2/3} log^{1/3}(AT/δ)`. The constant `C` is
universal: fixed once, before every instance parameter, matching the book's `≲`. -/
theorem epsilon_greedy_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (ε : ℝ), ε = ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / T) ^ ((1 : ℝ) / 3) →
        ∀ (piHat : ℕ → Fin A) (p : ℕ → Fin A → ℝ),
          -- Eq. (2.6): ε-Greedy plays the empirical maximizer with probability `1 - ε`
          -- and a uniform random decision with probability `ε`.
          (∀ t : ℕ, ∀ a : Fin A,
              p t a = (1 - ε) * (if a = piHat t then (1 : ℝ) else 0) + ε * (1 / A)) →
          ∀ (fhat : ℕ → Fin A → ℝ),
          (∀ t : ℕ, ∀ a : Fin A, fhat t a ≤ fhat t (piHat t)) →
          -- Eq. (2.9): the good event, holding with probability at least `1 - δ`.
          (∀ t ∈ Finset.range T, ∀ a : Fin A,
              |fhat t a - fStar a| ≤ Real.sqrt ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / (ε * (t + 1)))) →
          regret fStar piStar T p ≤
            C * (A : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) *
              (Real.log ((A : ℝ) * T / δ)) ^ ((1 : ℝ) / 3) := by sorry

end FoundationsRL.Bandits

