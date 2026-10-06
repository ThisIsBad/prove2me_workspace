import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_ValueDist
import Definitions.Def_CHMSPricing_SpmMatroid_SetSystem

namespace CHMSPricing.SpmMatroid

open MeasureTheory

variable {n : ℕ}

open Classical in
/-- One round of a sequential posted-price mechanism (§2.2, p. 4): with current served set `A`,
agent `i` is offered service at price `pᵢ` iff `A ∪ {i} ∈ 𝒥`, and accepts iff `pᵢ ≤ vᵢ`. -/
noncomputable def spmStep (J : SetSystem (Fin n)) (p v : Fin n → ℝ) (A : Finset (Fin n))
    (i : Fin n) : Finset (Fin n) :=
  if J.Feasible (insert i A) ∧ p i ≤ v i then insert i A else A

/-- The set of agents served after the first `k` rounds of the SPM with ordering `σ`
(`σ 0` is approached first) and prices `p`, at value profile `v`. -/
noncomputable def spmServedBefore (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p v : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  ((List.finRange n).take k).foldl (fun A k' => spmStep J p v A (σ k')) ∅

/-- The set `A` of agents served by the SPM at the end of the run. -/
noncomputable def spmServed (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n))
    (p v : Fin n → ℝ) : Finset (Fin n) :=
  spmServedBefore J σ p v n

/-- Agent `i` is offered service at its turn (position `σ⁻¹ i`): adding it to the set served
so far is feasible. -/
def spmOffered (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ)
    (i : Fin n) : Prop :=
  J.Feasible (insert i (spmServedBefore J σ p v (σ.symm i : ℕ)))

open Classical in
/-- The agents that are blocked: not offered service at their turn, because adding them to the
set served so far would be infeasible. -/
noncomputable def spmBlocked (J : SetSystem (Fin n)) (σ : Equiv.Perm (Fin n)) (p v : Fin n → ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬ spmOffered J σ p v i)

/-- `ℛ^σ_p`: the expected revenue `𝔼_v[∑_{i ∈ A} pᵢ]` of the SPM. -/
noncomputable def spmRevenue (D : Fin n → ValueDist) (J : SetSystem (Fin n))
    (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : ℝ :=
  ∫ v, ∑ i ∈ spmServed J σ p v, p i ∂(prior D)

end CHMSPricing.SpmMatroid
