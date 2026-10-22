import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Theorem 6.5, Dai & Harrison p. 116 (PDF p. 132): fix `ω` such that the SLLNs (2.14), (2.15)
for the core stochastic elements and the negligibility condition (6.38) all hold. For any
unbounded set `C ⊂ 𝒳` of initial states, there is a sequence `{xₙ} ⊂ C` with `|xₙ| → ∞` such
that the fluid-scaled processes (6.37) converge u.o.c. to some continuous
`(D̂, F̂, T̂, Ẑ) ∈ C^I × C^J × C^J × C^I` (6.39), and furthermore `(D̂, F̂, T̂, Ẑ)` satisfies the
fluid equations (6.1)-(6.6) with `|Ẑ(0)| = 1`. -/
theorem fluid_limit_existence
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    (E : Fin I → ℝ → Ω → ℕ) (v : Fin J → ℕ → Ω → ℝ) (φ : Fin J → ℕ → Ω → Fin I → ℕ) (ω : Ω)
    (C : Set Xstate) (hC : ¬ BddAbove ((spnSize Mrep) '' C))
    (h214 : ∀ i, Tendsto (fun t : ℝ => (E i t ω : ℝ) / t) atTop (nhds (dat.lam i)))
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)) ∧
        ∀ i, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n) atTop
          (nhds (dat.Γ i j)))
    (h638 :
      ∀ j, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v j ℓ ω) atTop
        (nhds 0)) :
    ∃ (x : ℕ → Xstate) (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ),
      (∀ n, x n ∈ C) ∧ Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
      Continuous Dh ∧ Continuous Fh ∧ Continuous Th ∧ Continuous Zh ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.D (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Dh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * (fam.F (x n) (spnSize Mrep (x n) * t) ω j : ℝ)) Fh ∧
      UOCConverges
        (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
      UOCConverges
        (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Zh ∧
      IsFluidModelSolution dat Dh Fh Th Zh ∧ (∑ i, Zh 0 i) = 1 := by sorry

end ProcessingNetworks.FluidStability

