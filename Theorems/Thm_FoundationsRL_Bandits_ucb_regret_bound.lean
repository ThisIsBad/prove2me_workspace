import Mathlib
import Definitions.Def_FoundationsRL_Bandits_regret
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_FoundationsRL_Bandits_confidenceRadius

namespace FoundationsRL.Bandits

/-- Proposition 5 (UCB regret, GOAL), Foster–Rakhlin p. 28. Assume `fStar π ∈ [0,1]`
for every decision `π`. Suppose `pi` is a realized UCB decision sequence following
the book's rule: at every round `t`, if some action is still unsampled then `pi t`
is one such unsampled action; once every action has been sampled at least once,
`pi t` maximizes the upper confidence bound `fhat t a + confidenceRadius` of
Eq. (2.19) among all actions `a`. Conditional on the event of Eq. (2.18) — that
this holds with probability at least `1 - δ`, restricted to rounds/actions where
the radius is meaningful (`n_t(π) ≠ 0`) since (2.18) is otherwise vacuous — the
UCB algorithm's regret satisfies `Reg ≲ √(AT log(AT/δ))`. The constant `C` is
universal: fixed once, before every instance parameter, matching the book's `≲`. -/
theorem ucb_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (pi : ℕ → Fin A) (fhat : ℕ → Fin A → ℝ),
          -- if some action is still unsampled, UCB plays an unsampled action
          -- (its upper confidence bound is `+∞` in the book).
          (∀ t : ℕ, (∃ a : Fin A, pullCount pi t a = 0) → pullCount pi t (pi t) = 0) →
          -- once every action has been sampled, `pi t` maximizes the upper confidence bound.
          (∀ t : ℕ, (∀ a : Fin A, pullCount pi t a ≠ 0) → ∀ a : Fin A,
              fhat t a + confidenceRadius T A δ (pullCount pi t a) ≤
                fhat t (pi t) + confidenceRadius T A δ (pullCount pi t (pi t))) →
          -- Eq. (2.18): the good event, holding with probability at least `1 - δ`,
          -- restricted to sampled actions (vacuous otherwise in the book).
          (∀ t ∈ Finset.range T, ∀ a : Fin A, pullCount pi t a ≠ 0 →
              |fhat t a - fStar a| ≤ confidenceRadius T A δ (pullCount pi t a)) →
          regret fStar piStar T (fun t a => if a = pi t then (1 : ℝ) else 0) ≤
            C * Real.sqrt ((A : ℝ) * T * Real.log ((A : ℝ) * T / δ)) := by sorry

end FoundationsRL.Bandits

