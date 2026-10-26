import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Lemma 3 of Anderson and Potts (2004), p. 690, for one instance: given an optimal schedule
`μ*` of (2P) and a feasible schedule `σ_E` of (E) satisfying inequality (1)
`∑_{j∈J} wⱼ Cⱼ(σ_E) + ∑_{g∈G} w_g C_g(σ_E) ≤ ∑_{j∈J} wⱼ Cⱼ(μ*) + ∑_{g∈G} w_g C_g(π_E)`,
the Delayed SWPT schedule costs at most twice any feasible schedule of (P). -/
theorem reduction {n : ℕ} (I : Instance n) (μstar : Fin n → ℕ)
    (hμ : IsOptimal (double I).r (double I).p (double I).w μstar)
    (σE : EJob I → ℕ) (hσ : IsFeasible (rE I) (pE I) σE)
    (h1 : ∑ j : Fin n, I.w j * ((σE (Sum.inl j) + I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((σE (Sum.inr g) + 1 : ℕ) : ℝ) ≤
        ∑ j : Fin n, I.w j * ((μstar j + 2 * I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((g.1 + 1 : ℕ) : ℝ))
    (S : Fin n → ℕ) (hS : IsFeasible I.r I.p S) :
    cost I.w I.p (dswpt I) ≤ 2 * cost I.w I.p S := by sorry

end DelayedSWPT.Extended

