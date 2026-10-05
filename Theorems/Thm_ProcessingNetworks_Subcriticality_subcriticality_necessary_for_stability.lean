import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions
import Definitions.Def_ProcessingNetworks_Stability_Stable
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_Subcriticality_SPNPlanningData
import Definitions.Def_ProcessingNetworks_Subcriticality_StaticPlanningProblem

namespace ProcessingNetworks.Subcriticality

open MeasureTheory ProcessingNetworks.Stability
open scoped NNReal

/-- Theorem 5.2 (only subcritical networks can be stable), p. 96 (PDF p. 112, crossing the page
break to PDF p. 113): consider either the basic SPN model of Section 2.3 (`IsBasicSPN`) or the
relaxed model of Section 2.4 under a simply structured policy (`IsRelaxedSPN`, with the service
rate vector `β(t)` a function of the ambient state `X(t)`, Remark 5.3), built on the model data
`dat` (Section 2.1) from the primitive stochastic elements `E, v, φ, Psi` and the initial data
`N0, Z0`. If the baseline stochastic assumptions (2.1) and the Markov representation (3.1) are
satisfied, and the SPN is stable, then its arrival-rate vector `lam` lies in the subcritical
region `Λ` (5.16) of the static planning problem with `R = (B - Γ)M⁻¹` (5.3), `A`, `b`. -/
theorem subcriticality_necessary_for_stability
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N0 : Fin J → ℕ} {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (ba : BaselineAssumptions I J N0 E lam v φ m Γ Psi)
    (dat : SPNData I J K) {Z0 : Fin I → ℕ}
    {S F N : ℝ → Ω → Fin J → ℕ} {T : ℝ → Ω → Fin J → ℝ} {D Z : ℝ → Ω → Fin I → ℕ}
    (M : MarkovRepresentation Xstate I J N Z)
    (hmodel : IsBasicSPN dat E v φ N0 Psi Z0 S F N T D Z ∨
      ∃ β : ℝ → Ω → Fin J → ℝ, IsRelaxedSPN dat E v φ N0 Psi Z0 S F N T D Z β ∧
        ∃ g : Xstate → Fin J → ℝ, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → β t ω = g (M.X t ω))
    (hstable : IsStable M) :
    (fun i => (lam i : ℝ)) ∈
      SubcriticalRegion (SPNPlanningData.ofOutputMatrix dat.B Γ m
        (fun j => (ba.mean_service_time j).2.2) dat.A dat.b dat.b_pos) := by sorry

end ProcessingNetworks.Subcriticality

