import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_PacketNetworkModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

/-- `S(z)` (Eq. 12.40): the schedules in `S` available at buffer contents `z`, i.e. satisfying
the packet availability constraint `Bs ≤ z` (Eq. 12.3). Phrased for `z : Fin I → ℝ` so the same
definition serves the discrete state (`z` cast from `Fin I → ℕ`, Lemmas 12.17-12.18, Theorem
12.16) and the fluid-scale state `Ẑ(t)` (Lemma 12.20). -/
noncomputable def feasibleSchedulesAt {I J : ℕ} (dat : PacketNetworkData I J)
    (S : Finset (Fin J → ℕ)) (z : Fin I → ℝ) : Finset (Fin J → ℕ) :=
  S.filter (fun s => ∀ i, (B dat).mulVec (realize s) i ≤ z i)

/-- The max-weight/back-pressure objective `z·Rs` (Eq. 12.41). -/
noncomputable def bpObjective {I J : ℕ} (dat : PacketNetworkData I J) (z : Fin I → ℝ)
    (s : Fin J → ℕ) : ℝ :=
  z ⬝ᵥ (R dat).mulVec (realize s)

/-- `s` solves the MW/BP optimization problem (12.41) at state `z`: `s ∈ S(z)` and `s` dominates
every alternative in `S(z)`. -/
def IsBPOptimal {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ)) (z : Fin I → ℝ)
    (s : Fin J → ℕ) : Prop :=
  s ∈ feasibleSchedulesAt dat S z ∧
  ∀ s' ∈ feasibleSchedulesAt dat S z, bpObjective dat z s' ≤ bpObjective dat z s

/-- The back-pressure (max-weight) control policy, Section 12.4: a Markovian policy `f` of (12.8)
that, in each timeslot, given the observed buffer contents `z`, chooses a schedule solving (12.41).
The randomization argument `u` is carried so that every "version" of the policy (every
tie-breaking rule, deterministic or randomized, Remark 12.19) is covered; `f` is then admissible
in the sense of Definition 12.3, since `S(z)` enforces (12.3). -/
def IsBackPressurePolicy {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (f : (Fin I → ℕ) → ℝ → (Fin J → ℕ)) : Prop :=
  ∀ z : Fin I → ℕ, ∀ uu : ℝ, 0 < uu → uu < 1 → IsBPOptimal dat S (fun i => (z i : ℝ)) (f z uu)

end ProcessingNetworks.PacketNetworks
