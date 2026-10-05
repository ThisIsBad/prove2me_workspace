import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Lemma 6.7, Dai & Harrison p. 116 (PDF p. 132): fix `ω`. For any unbounded set `C` of initial
states (unbounded meaning `{|x| : x ∈ C}` is unbounded in `ℝ`), there is a sequence `{xₙ} ⊂ C`
with `|xₙ| → ∞` such that `T̂^{xₙ}(·,ω) → T̂(·)` u.o.c. and `Ẑ^{xₙ}(0,ω) → Ẑ(0)` as `n → ∞`
(6.40), for some `T̂ ∈ C(ℝ≥0,ℝ^J)` and `Ẑ(0) ∈ ℝ^I_{≥0}`. -/
theorem fluid_limit_compactness
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω) (C : Set Xstate)
    (hC : ¬ BddAbove ((spnSize Mrep) '' C)) :
    ∃ (x : ℕ → Xstate) (Th : ℝ → Fin J → ℝ) (Zh0 : Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Th ∧ (∀ i, 0 ≤ Zh0 i) ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      Tendsto (fun n i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) 0 ω i : ℝ)) atTop (nhds Zh0) := by sorry

end ProcessingNetworks.FluidStability

