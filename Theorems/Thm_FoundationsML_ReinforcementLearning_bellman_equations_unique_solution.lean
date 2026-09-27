import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward

open Matrix

namespace FoundationsML.ReinforcementLearning

/-- Theorem 17.10 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 386, PDF p. 403). For a finite MDP, Bellman's equations admit a unique
solution given by `V_π = (I − γP)⁻¹R`, where `P` is the transition-probability matrix induced
by the fixed policy `π` (`P_{s,s'} = P[s'|s,π(s)]`) and `R` is its induced expected-reward
vector (`R_s = E[r(s,π(s))]`).

**Formalization Note.** `P` in `(I − γP)` is `Matrix.of (InducedTransition π P)`, the matrix
induced by the *fixed* policy `π` (not the raw MDP kernel indexed by an unfixed action), per
`BRIEF.md`'s pitfall note. The three conjuncts state: (i) `(I − γP)` is invertible — proved in
the book via the operator-norm bound `‖γP‖∞ = γ < 1`, genuine linear-algebra content, not
unfolding; (ii) the actual policy value `V_π` (`PolicyValue`) equals the closed-form solution
`(I−γP)⁻¹R`; and (iii) uniqueness — any `V` satisfying the Bellman equations (17.6) equals that
same closed form. -/
theorem bellman_equations_unique_solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsUnit (1 - γ • (Matrix.of (InducedTransition π P))) ∧
    (fun s => PolicyValue π P Er γ s) =
      (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er ∧
    ∀ V : S → ℝ,
      (∀ s : S, V s = InducedReward π Er s + γ * ∑ s' : S, InducedTransition π P s s' * V s') →
        V = (1 - γ • (Matrix.of (InducedTransition π P)))⁻¹ *ᵥ InducedReward π Er := by sorry

end FoundationsML.ReinforcementLearning
