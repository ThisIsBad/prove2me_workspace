import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem
import Definitions.Def_ProcessingNetworks_Subcriticality_BaselineAssumptionsMArP

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProcessingNetworks.Stability

/-- Corollary 5.4 (Markovian arrival process), p. 99 (PDF p. 115): Theorem 5.2 remains valid when
Assumption 2.1 is weakened to allow a Markovian arrival process (`BaselineAssumptionsMArP`), with
`lam` now the I-vector of long-run arrival rates given by the MArP's own SLLN (Proposition E.7(a))
rather than by (2.14)'s Poisson-specific SLLN. The model hypotheses (basic or relaxed SPN on the
data `dat`, Markov representation in the augmented form (4.4), stability) are those of
`subcriticality_necessary_for_stability`. -/
theorem subcriticality_necessary_markovian_arrival_process
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (ba : BaselineAssumptionsMArP I J E lam v φ m Γ Psi)
    (dat : SPNData I J K) {N0 : Fin J → ℕ} {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M) :
    lam ∈ SubcriticalRegion (SPNPlanningData.ofOutputMatrix dat.B Γ m
      (fun j => (ba.mean_service_time j).2.2) dat.A dat.b dat.b_pos) := by sorry

end ProcessingNetworks.Subcriticality

