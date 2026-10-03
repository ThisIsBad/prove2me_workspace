import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

namespace ProcessingNetworks.BackPressure

open MeasureTheory

open Filter

/-- Lemma 9.11, Dai & Harrison p. 175 (PDF p. 191): given that Assumption 9.1 holds, each fluid
limit path `(D̂,F̂,T̂,Ẑ,Ŷ)` under the relaxed back-pressure control policy satisfies the basic
fluid equations (6.1)-(6.6) plus (9.28)-(9.31). The raw ("pre-limit") meaning of "operating under
relaxed back-pressure control" is formalized via `hYopt`: a strictly dominated allocation accrues
no additional processing time throughout any raw time interval over which it stays strictly
dominated — the operational content of always selecting an optimal allocation, from which
(9.31)'s fluid-scale statement is obtained by a genuine limit-passage argument (not reproduced
here; see `MODERATION_NOTES.md`). -/
theorem relaxed_bp_extended_fluid_equations
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = ExtremeAllocations dat)
    (Zraw Traw : Xstate → ℝ → Ω → Fin I → ℝ) (Yraw : (Fin J → ℝ) → Xstate → ℝ → Ω → ℝ)
    (Traw' : Xstate → ℝ → Ω → Fin J → ℝ)
    (size : Xstate → ℝ) (size_nonneg : ∀ x, 0 ≤ size x)
    (hTY : ∀ x ω t j, Traw' x t ω j = ∑ β ∈ E, β j * Yraw β x t ω)
    (hYmono : ∀ β ∈ E, ∀ x ω, Monotone (Yraw β x · ω))
    (hYsum : ∀ x ω t, 0 ≤ t → ∑ β ∈ E, Yraw β x t ω = t)
    (hYopt : ∀ β ∈ E, ∀ (x : Xstate) (ω : Ω) (u1 u2 : ℝ), 0 ≤ u1 → u1 ≤ u2 →
      (∀ u ∈ Set.Icc u1 u2, p dat β (Zraw x u ω) < ⨆ α ∈ E, p dat α (Zraw x u ω)) →
      Yraw β x u2 ω = Yraw β x u1 ω)
    (ω : Ω) (x : ℕ → Xstate) (hsize : Tendsto (fun n => size (x n)) atTop atTop)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) (Yh : (Fin J → ℝ) → ℝ → ℝ)
    (hZconv :
      UOCConverges (fun n t i => (size (x n))⁻¹ * Zraw (x n) (size (x n) * t) ω i) Zh)
    (hTconv :
      UOCConverges (fun n t j => (size (x n))⁻¹ * Traw' (x n) (size (x n) * t) ω j) Th)
    (hYconv : ∀ β ∈ E,
      UOCConvergesR (fun n t => (size (x n))⁻¹ * Yraw β (x n) (size (x n) * t) ω) (Yh β)) :
    (∀ t : ℝ, 0 ≤ t → ∀ j, Th t j = ∑ β ∈ E, β j * Yh β t) ∧
    (∀ β ∈ E, Monotone (Yh β)) ∧
    (∀ t : ℝ, 0 ≤ t → ∑ β ∈ E, Yh β t = t) ∧
    (∀ β ∈ E, ∀ t : ℝ, 0 < t → p dat β (Zh t) < ⨆ α ∈ E, p dat α (Zh t) →
      ∀ d : ℝ, HasDerivAt (Yh β) d t → d = 0) := by sorry

end ProcessingNetworks.BackPressure
