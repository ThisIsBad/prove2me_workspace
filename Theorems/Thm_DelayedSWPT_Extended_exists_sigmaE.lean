import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

namespace DelayedSWPT.Extended

open DelayedSWPT.Model

/-- Anderson and Potts (2004), §§3.4–3.6, proof of Theorem 8, p. 696: from an optimal schedule
`μ*` of (2P) one can construct a feasible schedule `σ_E` of (E) satisfying inequality (1)
`∑_{j∈J} wⱼ Cⱼ(σ_E) + ∑_{g∈G} w_g C_g(σ_E) ≤ ∑_{j∈J} wⱼ Cⱼ(μ*) + ∑_{g∈G} w_g C_g(π_E)`. -/
theorem exists_sigmaE {n : ℕ} (I : Instance n) (μstar : Fin n → ℕ)
    (hμ : IsOptimal (double I).r (double I).p (double I).w μstar) :
    ∃ σE : EJob I → ℕ, IsFeasible (rE I) (pE I) σE ∧
      ∑ j : Fin n, I.w j * ((σE (Sum.inl j) + I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((σE (Sum.inr g) + 1 : ℕ) : ℝ) ≤
        ∑ j : Fin n, I.w j * ((μstar j + 2 * I.p j : ℕ) : ℝ) +
          ∑ g : gapTimes I, gapWeight I g * ((g.1 + 1 : ℕ) : ℝ) := by sorry

end DelayedSWPT.Extended

