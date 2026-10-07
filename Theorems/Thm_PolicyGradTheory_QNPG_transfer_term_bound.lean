import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning

/-- Inequality (25), proof of Theorem 6.1, p. 39. The displayed proof
uses no minimizing property of its weight vector. -/
theorem transfer_term_bound {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] {d : ℕ}
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (θ w : EuclideanSpace ℝ (Fin d)) :
    (∑ s : S, PolicyGradTheory.ProjGA.visitation πstar P γ ρ s *
      ∑ a : A, πstar s a *
        (PolicyGradTheory.ProjGA.advantage (logLinearPolicy φ θ) P r γ s a -
          inner ℝ w (gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ))) ≤
      2 * Real.sqrt ((Fintype.card A : ℝ) *
        qLoss P r γ φ w θ (dstar P γ ρ πstar)) := by sorry

end PolicyGradTheory.QNPG

