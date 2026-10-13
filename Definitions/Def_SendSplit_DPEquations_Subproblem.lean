import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network

namespace SendSplit.DPEquations

/-- The demand nodes `D = {i : r_i ≠ 0}` (p. 638). -/
noncomputable def demandNodes {n : ℕ} (r : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => r i ≠ 0)

/-- The index sets of the send-and-split equations: `∅ ⊂ I ⊆ D`. -/
def IsAdmissible {n : ℕ} (r : Fin n → ℝ) (I : Finset (Fin n)) : Prop :=
  I.Nonempty ∧ I ⊆ demandNodes r

/-- `r_I ≡ Σ_{j ∈ I} r_j` (p. 640). -/
def demandSum {n : ℕ} (r : Fin n → ℝ) (I : Finset (Fin n)) : ℝ :=
  ∑ j ∈ I, r j

/-- The demand vector of the subproblem `i → I` (p. 640): replace `r_j` by zero for all
`j ∉ I`, then subtract `r_I` from the resulting demand at node `i`. -/
def subDemand {n : ℕ} (r : Fin n → ℝ) (i : Fin n) (I : Finset (Fin n)) : Fin n → ℝ :=
  fun k => (if k ∈ I then r k else 0) - (if k = i then demandSum r I else 0)

/-- `C_iI` (p. 640): the minimum cost among all flows for the subproblem `i → I`, as an
extended real; it is `+∞` (the empty infimum) when the subproblem has no flow. -/
noncomputable def minCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (i : Fin n) (I : Finset (Fin n)) : EReal :=
  ⨅ (x : Fin n → Fin n → ℝ) (_ : IsFlow A (subDemand r i I) x), ((flowCost A c x : ℝ) : EReal)

end SendSplit.DPEquations
