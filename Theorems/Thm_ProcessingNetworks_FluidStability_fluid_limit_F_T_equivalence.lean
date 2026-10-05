import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Lemma 6.8, Dai & Harrison p. 116 (PDF p. 132): fix `ω` at which the SLLN (2.15) for service
times and the negligibility condition (6.38) both hold. For an arbitrary sequence of initial
states `{xₙ}` and an arbitrary sequence of scaling parameters `{rₙ} ⊂ ℝ_{≥0}` with `rₙ → ∞`, and
each `t ≥ 0`: `lim_{n→∞} (1/rₙ) F^{xₙ}_j(rₙt,ω)` exists iff `lim_{n→∞} (1/rₙ) T^{xₙ}_j(rₙt,ω)`
exists (6.41)-(6.42); furthermore, denoting by `F̂_j(t)`, `T̂_j(t)` the limits when they exist,
`m_j F̂_j(t) = T̂_j(t)` (6.43). -/
theorem fluid_limit_F_T_equivalence
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω)
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0))
    (x : ℕ → Xstate) (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) (t : ℝ) (ht : 0 ≤ t) (j : Fin J) :
    ((∃ Fhj : ℝ, Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj)) ↔
     (∃ Thj : ℝ, Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj))) ∧
    (∀ Fhj Thj : ℝ,
      Tendsto (fun n => (r n)⁻¹ * (fam.F (x n) (r n * t) ω j : ℝ)) atTop (nhds Fhj) →
      Tendsto (fun n => (r n)⁻¹ * fam.T (x n) (r n * t) ω j) atTop (nhds Thj) →
      dat.m j * Fhj = Thj) := by sorry

end ProcessingNetworks.FluidStability

