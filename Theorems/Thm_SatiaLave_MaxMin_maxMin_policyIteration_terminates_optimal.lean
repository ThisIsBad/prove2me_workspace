import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- Proposition 5, p. 732 (with Proposition 3, p. 731): along every run `A 0, A 1, …` of the
max-min policy-iteration algorithm, the max-min returns increase monotonically, and within
fewer than `|Policy|` iterations the algorithm terminates (`A (n+1) = A n`) at a policy that is
max-min optimal, attains the solution of (4), and is `ε`-optimal for every `ε > 0`. -/
theorem maxMin_policyIteration_terminates_optimal {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A : ℕ → Policy S D) (hrun : ∀ n, IsPhase2Step M (A n) (A (n + 1))) :
    (∀ n i, robustValue M (A n) i ≤ robustValue M (A (n + 1)) i) ∧
      ∃ n, n < Fintype.card (Policy S D) ∧ A (n + 1) = A n ∧ IsMaxMinOptimal M (A n) ∧
        (∀ v : S → ℝ, (∀ j, v j = eq4Op M v j) → ∀ j, robustValue M (A n) j = v j) ∧
        ∀ ε > 0, IsEpsMaxMinOptimal M ε (A n) := by sorry

end SatiaLave.MaxMin

