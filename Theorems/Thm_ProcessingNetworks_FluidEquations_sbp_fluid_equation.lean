import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_Hset
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations

namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

/-- Theorem 7.3, Dai & Harrison p. 128 (PDF p. 144): for a queueing network operating under a
non-preemptive static-buffer-priority (SBP) policy with priority ranking `σ`
(`SBPNonPreemptive dat σ fam`, the two-sided bound (7.7)), each fluid limit path satisfies the
fluid equation (7.6): for each buffer `j` and each `t > 0`, `∑_{i∈H(j)} Ẑᵢ(t) > 0` implies
`d/dt (∑_{i∈H(j)} T̂ᵢ(t)) = b_{p(j)}`. The fluid limit path is given by its witnessing sample
point `ω` and initial-state sequence `x` (the proof's (7.8)–(7.9) use the condition (6.38) at
that `ω`, `(1/n) max_{ℓ ≤ n} v_i(ℓ) → 0`, to show the remaining-processing-time term of (7.7)
is negligible), together with the u.o.c. convergences (6.39) along `(ω, x)`. -/
theorem sbp_fluid_equation
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ)
    (σ : Equiv.Perm (Fin I)) (hsbp : SBPNonPreemptive dat σ fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
    (h638 : ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v i ℓ ω) atTop (nhds 0))
    (hDcont : Continuous Dh) (hFcont : Continuous Fh) (hTcont : Continuous Th)
    (hZcont : Continuous Zh) (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hD : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.D (x n) (Mrep.size (x n) * t) ω i : ℝ)) Dh)
    (hF : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω i : ℝ)) Fh)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh)
    (j : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ Hset dat σ j, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ Hset dat σ j, Th s i) (dat.b (dat.p j)) t := by sorry

end ProcessingNetworks.FluidEquations

