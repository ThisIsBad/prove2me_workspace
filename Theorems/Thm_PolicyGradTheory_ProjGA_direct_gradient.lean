import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open FoundationsML.ReinforcementLearning

namespace PolicyGradTheory.ProjGA

/-- (7), §4, arXiv:1908.00261v5, p. 13: for the direct parameterization, at every policy `π`,
`∂V^π(μ)/∂π(a|s) = (1/(1−γ)) d^π_μ(s) Q^π(s,a)`; the Euclidean gradient of `π ↦ V^π(μ)` has
these coordinates. -/
theorem direct_gradient {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : IsFiniteMDP P r γ) (μ : S → ℝ) :
    ∀ π ∈ simplexSet S A, ∀ (s : S) (a : A),
      gradient (directValue P r γ μ) π (s, a) =
        1 / (1 - γ) * visitation (asPolicy π) P γ μ s * QFunction (asPolicy π) P r γ s a := by sorry

end PolicyGradTheory.ProjGA

