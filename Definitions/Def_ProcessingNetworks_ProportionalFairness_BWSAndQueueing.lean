import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel

namespace ProcessingNetworks.ProportionalFairness

/-- The data of a bandwidth sharing (BWS) network (Section 4.5), restated locally per this
chunk's own `BRIEF.md` pitfall note (mission II's own `BRIEF.md` did not pull the BWS/HLPPS
definitions from Chapter 4): `I`-vectors `lam`, `m`, and a `K × I` capacity consumption matrix
`Amat` with capacities `bvec` (single-hop: no routing between classes). -/
structure BWSNetworkData (I K : ℕ) where
  lam : Fin I → ℝ
  m : Fin I → ℝ
  hm : ∀ i, 0 < m i
  Amat : Matrix (Fin K) (Fin I) ℝ
  bvec : Fin K → ℝ

/-- The standard load condition `ρ < b` (Eq. 5.1) for a BWS network: `A(λ ⊙ m) < b`
componentwise (single-hop, so the total arrival rate vector is `λ` itself). -/
def BWSLoadCondition {I K : ℕ} (dat : BWSNetworkData I K) : Prop :=
  ∀ k, (dat.Amat.mulVec (fun i => dat.lam i * dat.m i)) k < dat.bvec k

/-- The data of a queueing network (Section 2.6) under HLPPS control (Section 4.6): `I`-vectors
`lam`, `m`, an `I × I` routing matrix `P`, an assignment `server : Fin I → Fin K` of each class to
the single server that processes it, and server capacities `b > 0`. -/
structure QueueingNetworkDataHL (I K : ℕ) where
  lam : Fin I → ℝ
  m : Fin I → ℝ
  hm : ∀ i, 0 < m i
  P : Matrix (Fin I) (Fin I) ℝ
  server : Fin I → Fin K
  b : Fin K → ℝ
  hb : ∀ k, 0 < b k

/-- HLPPS fluid stability (Section 10.6, "Queueing network with HLPPS control"): the PF fluid
model specialized to `grp := server` and `TildeAllocSet := ∏_k [0,b_k]` (Eq. 10.78), the box under
which the aggregate PF allocation function `ψ̃` coincides with HLPPS's own per-server capacity
allocation. -/
def HLPPSFluidStable {I K : ℕ} (dat : QueueingNetworkDataHL I K) : Prop :=
  PFFluidStable (I := I) (L := K)
    ⟨dat.lam, dat.m, dat.hm, dat.P, dat.server, {y : Fin K → ℝ | ∀ k, 0 ≤ y k ∧ y k ≤ dat.b k}⟩

end ProcessingNetworks.ProportionalFairness
