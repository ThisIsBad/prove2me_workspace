import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount

namespace FoundationsRL.Bandits

/-- Lemma 8 (Confidence width potential lemma), Foster–Rakhlin p. 28–29:
for any realized decision sequence over `A` actions and horizon `T`,
`Σ_{t=1}^T (1/√(n_t(π_t)) ∧ 1) ≲ √(AT)`, where `n_t(π_t) = 0` contributes
the capped value `1` (the `∧ 1` convention). The constant `C` is universal:
fixed once, before the action count `A`, horizon `T`, and decision sequence
`pi` are quantified, matching the book's `≲`. -/
theorem confidence_width_potential_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (T : ℕ) (pi : ℕ → Fin A),
        ∑ t ∈ Finset.range T,
            (if pullCount pi t (pi t) = 0 then (1 : ℝ)
              else 1 / Real.sqrt (pullCount pi t (pi t)))
          ≤ C * Real.sqrt ((A : ℝ) * T) := by sorry

end FoundationsRL.Bandits

