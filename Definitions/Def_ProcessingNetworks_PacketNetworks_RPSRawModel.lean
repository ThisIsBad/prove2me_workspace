import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_PacketNetworkModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion
import Definitions.Def_ProcessingNetworks_PacketNetworks_MarkovianPolicy
import Definitions.Def_ProcessingNetworks_ProportionalFairness_PFOptimization
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel

namespace ProcessingNetworks.PacketNetworks

open MeasureTheory

/-- A packet network with fixed routing (Section 12.6): the special case `J = I` in which
activity `i` processes packets of class `i` (`u = id`, so `B` is the identity), together with the
link structure of Section 12.2 (`K` links, feasible configurations `C`) and the link designation
`linkDesig i = k` (`A_{ki} = 1`: class `i` packets traverse link `k` in the one service type
available to them; `I(k)` is the set of classes belonging to link `k`). -/
structure FixedRoutingData (I K : ℕ) where
  dat : PacketNetworkData I I
  u_id : dat.u = id
  cfg : LinkConfigData I K
  linkDesig : Fin I → Fin K
  A_desig : ∀ k i, cfg.A k i = if linkDesig i = k then 1 else 0

/-- The routing matrix `P` of Section 12.6: `P_{ij} = 1` if class `i` packets become class `j`
packets after completing their one service (`R_{ji} = −1`), `0` otherwise; `R = I − P'` (12.48). -/
def RouteMatrix {I K : ℕ} (fr : FixedRoutingData I K) : Matrix (Fin I) (Fin I) ℝ :=
  fun i j => if fr.dat.d i = some j then (1 : ℝ) else 0

/-- The classes belonging to link `k`, `I(k)` (Section 12.6). -/
def linkClasses {I K : ℕ} (fr : FixedRoutingData I K) (k : Fin K) : Finset (Fin I) :=
  Finset.univ.filter (fun i => fr.linkDesig i = k)

/-- `y = Az`, the `K`-vector of link-level packet counts (Section 12.6). -/
def linkCounts {I K : ℕ} (fr : FixedRoutingData I K) (z : Fin I → ℕ) : Fin K → ℕ :=
  fun k => ∑ i ∈ linkClasses fr k, z i

/-- The data of the PF fluid model of Section 10.4 that the RPS fluid model instantiates
(Proposition 12.26): the `I` packet classes as job classes, unit service times, routing matrix
`P`, one demand group per link (`L = K`, `grp = linkDesig`), and `⟨C⟩` in the role of `Ã`. -/
noncomputable def toPFData {I K : ℕ} (fr : FixedRoutingData I K) (lam : Fin I → ℝ) :
    ProportionalFairness.PFUnitaryNetworkData I K :=
  ⟨lam, fun _ => 1, fun _ => one_pos, RouteMatrix fr, fr.linkDesig, hullFinset fr.cfg.C⟩

/-- Steps (c)–(d) of the random proportional scheduler (Section 12.6): given class-level counts
`z` and the configuration `c` of the timeslot, `x_k = c_k ∧ y_k` packets are transferred over link
`k`, selected uniformly at random without replacement from the `y_k` packets awaiting transfer over
that link. `selectionProb fr z c s` is the probability that this selection transfers exactly `s_i`
packets from each buffer `i` (a product over links of multivariate hypergeometric weights; zero
unless `∑_{i ∈ I(k)} s_i = c_k ∧ y_k` for every `k`). -/
noncomputable def selectionProb {I K : ℕ} (fr : FixedRoutingData I K) (z : Fin I → ℕ)
    (c : Fin K → ℕ) (s : Fin I → ℕ) : ℝ :=
  ∏ k : Fin K,
    (if ∑ i ∈ linkClasses fr k, s i = min (c k) (linkCounts fr z k) then
      (∏ i ∈ linkClasses fr k, ((z i).choose (s i) : ℝ)) /
        ((linkCounts fr z k).choose (min (c k) (linkCounts fr z k)) : ℝ)
    else 0)

/-- Walton's random proportional scheduler (Section 12.6, steps (a)–(d), with (12.55)–(12.57) and
(12.61)), as a Markovian policy `f(z,u)` of (12.8) in a fixed-routing network with schedule set
`S`. There is a map `σ(y,·) : (0,1) → C` such that, for every link-count vector `y = Az`: (a)–(b)
the randomized configuration `σ(y,U)` (`U` uniform on `(0,1)`) has mean vector `ĉ = ψ(y)`, a
solution of the RPS optimization problem (12.57), `max {∑_k y_k log ĉ_k : ĉ ∈ ⟨C⟩}`; and (c)–(d)
conditionally on the configuration `c`, the schedule `f(z,u)` is the random selection
`selectionProb fr z c`. The policy is admissible in the sense of Definition 12.3. -/
def IsRPSPolicy {I K : ℕ} (fr : FixedRoutingData I K) (S : Finset (Fin I → ℕ))
    (f : (Fin I → ℕ) → ℝ → (Fin I → ℕ)) : Prop :=
  IsAdmissibleMarkovianPolicy fr.dat S f ∧
  ∃ σ : (Fin K → ℕ) → ℝ → (Fin K → ℕ),
    (∀ y, Measurable (σ y)) ∧
    (∀ y : Fin K → ℕ, ∀ uu : ℝ, 0 < uu → uu < 1 → σ y uu ∈ fr.cfg.C) ∧
    (∀ y : Fin K → ℕ, ∃ chat : Fin K → ℝ,
      ProportionalFairness.IsPFMaximizer (hullFinset fr.cfg.C) (fun k => (y k : ℝ)) chat ∧
      ∀ k, ∫ uu in Set.Ioo (0 : ℝ) 1, (σ y uu k : ℝ) = chat k) ∧
    (∀ z : Fin I → ℕ, ∀ c ∈ fr.cfg.C, ∀ s : Fin I → ℕ,
      volume {uu ∈ Set.Ioo (0 : ℝ) 1 | σ (linkCounts fr z) uu = c ∧ f z uu = s} =
        volume {uu ∈ Set.Ioo (0 : ℝ) 1 | σ (linkCounts fr z) uu = c} *
          ENNReal.ofReal (selectionProb fr z c s))

end ProcessingNetworks.PacketNetworks
