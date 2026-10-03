import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

namespace ProcessingNetworks.BackPressure

/-- Theorem 9.12, Dai & Harrison p. 177 (PDF p. 193) — the goal theorem of this mission: consider
a Leontief network operating under the relaxed back-pressure control policy. If the static
planning problem has optimal objective value `γ* < 1`, then the fluid limit is stable (and hence,
by Theorem 6.2, the network's ambient Markov chain is positive recurrent). The arrival-rate vector
is nonnegative and the capacity consumption matrix nonnegative with no zero column (Section 2.1),
so that the allocation polytope is bounded and `z`-maximal allocations exist. The conclusion is
stability of the relaxed-BP fluid model (Definition 6.3 for (6.1)–(6.6) + (9.22)), which is what
the book's Lyapunov proof establishes and which implies fluid limit stability via Theorem 9.8. -/
theorem bp_maximal_stability
    {I J K : ℕ} (dat : SPNPlanningData I J K) (hleontief : IsLeontiefNetwork dat)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (lam : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (γstar : ℝ) (hopt : IsOptimalSPPValue dat lam γstar) (hsub : γstar < 1) :
    RelaxedBPFluidStable dat lam := by sorry

end ProcessingNetworks.BackPressure
