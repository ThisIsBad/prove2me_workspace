import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_RPSFluidModel

namespace ProcessingNetworks.PacketNetworks

/-- Proposition 12.26, Dai & Harrison p. 251 (PDF p. 267): the RPS fluid model is a special case
of the PF fluid model of Section 10.4, with the correspondences: the `I` packet classes play the
role of job classes; one demand group per link, `L = K`; the partition `{I(k), k ∈ K}` is the link
designation; and `⟨C⟩` plays the role of `Ã` in (10.23). Concretely, under Assumption 12.1, every
RPS fluid model solution `(D̂,T̂,Ẑ)` yields a PF fluid model solution `(Â, D̂, D̂, Ẑ)` at the data
`toPFData fr lam` (unit service times, so PF's `D = T/m = T`), with the PF arrival process
`Â(t) = λt + P'D̂(t)` (10.31). -/
theorem rps_fluid_model_eq_pf_fluid_model
    {I K : ℕ} (fr : FixedRoutingData I K) (h121 : SatisfiesAssumption121 fr.dat)
    (S : Finset (Fin I → ℕ)) (lam : Fin I → ℝ)
    (Dh : ℝ → Fin I → ℝ) (Th : ℝ → (Fin I → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ)
    (h : IsRPSFluidModelSolution fr S lam Dh Th Zh) :
    ProportionalFairness.IsPFFluidModelSolution (toPFData fr lam)
      (fun t i => lam i * t + ∑ k, RouteMatrix fr k i * Dh t k) Dh Dh Zh := by sorry

end ProcessingNetworks.PacketNetworks
