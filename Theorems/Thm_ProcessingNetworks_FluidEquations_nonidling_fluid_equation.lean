import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations

namespace ProcessingNetworks.FluidEquations

open MeasureTheory ProcessingNetworks.Stability

/-- Theorem 7.2, Dai & Harrison p. 126 (PDF p. 142): for a queueing network operating under a
non-idling policy (`NonIdling dat fam`, the sample-path identity (7.4)), each fluid limit path
satisfies the fluid equation (7.1): for each pool `k` and each `t > 0`, `∑_{i∈I(k)} Ẑᵢ(t) > 0`
implies `d/dt (∑_{i∈I(k)} T̂ᵢ(t)) = bₖ`. -/
theorem nonidling_fluid_equation
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hni : NonIdling dat fam)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) (dat.b k) t := by sorry

end ProcessingNetworks.FluidEquations

