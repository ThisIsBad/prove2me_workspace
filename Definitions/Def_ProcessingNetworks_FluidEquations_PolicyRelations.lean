import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_Hset

namespace ProcessingNetworks.FluidEquations

open MeasureTheory ProcessingNetworks.Stability

/-- A non-idling policy (Section 7.1: "no server remains idle while there is a job waiting in any
of the buffers that are processed by that server"), at the level of the sample paths of the
standard setup: whenever, throughout `[u₁, u₂]`, the buffers of pool `k` hold at least `bₖ` jobs
(so that all `bₖ` servers of the pool are busy, no server being allowed to idle while a job
waits), pool `k` works at its full capacity, `∑_{i∈I(k)} (T^x_i(u₂) - T^x_i(u₁)) = (u₂ - u₁) bₖ`
— the identity (7.4) used in the proof of Theorem 7.2. -/
def NonIdling {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) : Prop :=
  ∀ (x : Xstate) (ω : Ω) (u1 u2 : ℝ) (k : Fin K), 0 ≤ u1 → u1 ≤ u2 →
    (∀ u ∈ Set.Icc u1 u2, dat.b k ≤ ∑ i ∈ poolBuffers dat k, (fam.Zx x u ω i : ℝ)) →
    ∑ i ∈ poolBuffers dat k, (fam.T x u2 ω i - fam.T x u1 ω i) = (u2 - u1) * dat.b k

/-- The non-preemptive static buffer priority policy with ranking `σ` (Section 7.2), at the level
of the sample paths of the standard setup: the two-sided bound (7.7) of the proof of Theorem 7.3.
Whenever, throughout `[u₁, u₂]`, the buffers `H(j)` of priority at least that of `j` hold more
than `b_{p(j)}` jobs, the effort pool `p(j)` devotes to them over `[u₁, u₂]` is at most
`(u₂ - u₁) b_{p(j)}` and at least that quantity minus the total remaining processing time at `u₁`
of the jobs then in service at the pool — bounded, as in the book's proof, by the number of
servers times the largest service time of any job of a class of the pool started by `u₁`
(`delayedMax` over the first `F^x_i(u₁) + N^x_i(u₁)` service times of class `i`, in the order of
`L_i`). -/
def SBPNonPreemptive {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    (σ : Equiv.Perm (Fin I))
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) : Prop :=
  ∀ (x : Xstate) (ω : Ω) (u1 u2 : ℝ) (j : Fin I), 0 ≤ u1 → u1 ≤ u2 →
    (∀ u ∈ Set.Icc u1 u2, dat.b (dat.p j) < ∑ i ∈ Hset dat σ j, (fam.Zx x u ω i : ℝ)) →
    (u2 - u1) * dat.b (dat.p j) -
        dat.b (dat.p j) * (⨆ i ∈ poolBuffers dat (dat.p j),
          delayedMax (Mrep.f x).1 (fam.Psi x) v φ i (fam.F x u1 ω i + fam.Nx x u1 ω i) ω) ≤
      ∑ i ∈ Hset dat σ j, (fam.T x u2 ω i - fam.T x u1 ω i) ∧
    ∑ i ∈ Hset dat σ j, (fam.T x u2 ω i - fam.T x u1 ω i) ≤ (u2 - u1) * dat.b (dat.p j)

/-- The cumulative arrivals `G^x_i(t) = E_i(t) + ∑_j Φ^j_i(D^x_j(t))` into class `i`, external and
internal, Eq. (7.10), for the version of the SPN with initial state `x`. -/
def arrivals {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} {sd : SPNData I I K}
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep sd E v φ) (x : Xstate) (t : ℝ) (ω : Ω) (i : Fin I) : ℕ :=
  E i t ω + ∑ j, cumulativeOutput (Mrep.f x).1 (fam.Psi x) v φ j (fam.D x t ω j) ω i

/-- The immediate workload `W^x_k(t)` of server `k` at time `t`, Eq. (7.11):
`W(t) = A V(G(t) + Z(0)) - A T(t)`, the total work for server `k` that has arrived up to `t`
(`V_i(n)` the delayed random walk, the sum of the first `n` class-`i` service times in the order
of `L_i`) minus the total time server `k` has been busy up to `t`. -/
noncomputable def workload {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω]
    {I K : ℕ} {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (x : Xstate) (t : ℝ) (ω : Ω) (k : Fin K) :
    ℝ :=
  ∑ i ∈ poolBuffers dat k,
    (delayedWalk (Mrep.f x).1 (fam.Psi x) v φ i (arrivals fam x t ω i + (Mrep.f x).2 i) ω -
      fam.T x t ω i)

/-- The FCFS control policy (Section 7.3), in the single-server-pool setting the book restricts
to (`bₖ = 1`), at the level of the sample paths of the standard setup: the key identity (7.12),
`D_i(t + W_k(t)) = Z_i(0) + G_i(t)` for `i ∈ I(k)` — all jobs of station `k` present at time `t`
are completed exactly at `t + W_k(t)`, since later arrivals have lower priority. -/
def FCFS {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) : Prop :=
  (∀ k, dat.b k = 1) ∧
  ∀ (x : Xstate) (ω : Ω) (t : ℝ) (k : Fin K) (i : Fin I), 0 ≤ t → i ∈ poolBuffers dat k →
    fam.D x (t + workload dat fam x t ω k) ω i = (Mrep.f x).2 i + arrivals fam x t ω i

end ProcessingNetworks.FluidEquations
