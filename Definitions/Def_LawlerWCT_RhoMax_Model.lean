import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.RhoMax

/-- §7, p. 15: the weight of `I` with respect to the trial weights `w̄_j = w_j − ρ p_j`. -/
def trialWeight {ι : Type*} (p w : ι → ℝ) (ρ : ℝ) (I : Finset ι) : ℝ :=
  ∑ j ∈ I, (w j - ρ * p j)

/-- The nodes of the flow network `G*` of §7, p. 14: a source `s`, a sink `t`, and one node per job. -/
inductive Node (ι : Type*) where
  | s : Node ι
  | t : Node ι
  | job (j : ι) : Node ι
  deriving DecidableEq

open Classical in
/-- Capacities of `G*` (§7, p. 14): `c_sj = max(0, −w_j)`, `c_jt = max(0, +w_j)`, `c_ij = +∞` for
each arc `(i, j)` of `G`; a pair that is not an arc of `G*` has capacity `0`. -/
noncomputable def cap {ι : Type*} (G : ι → ι → Prop) (w : ι → ℝ) :
    Node ι → Node ι → WithTop ℝ
  | .s, .job j => ((max 0 (-w j) : ℝ) : WithTop ℝ)
  | .job j, .t => ((max 0 (w j) : ℝ) : WithTop ℝ)
  | .job i, .job j => if G i j then ⊤ else 0
  | _, _ => 0

/-- The node set `{s, t} ∪ N` of `G*`. -/
def nodes {ι : Type*} [DecidableEq ι] (N : Finset ι) : Finset (Node ι) :=
  {Node.s, Node.t} ∪ N.image Node.job

/-- The capacity `c(S, T) = ∑_{u ∈ S} ∑_{v ∈ T} c_uv` of the `(s, t)` cutset with sink side `T`
and source side `S = nodes N \ T`. -/
noncomputable def cutCapacity {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (w : ι → ℝ) (T : Finset (Node ι)) : WithTop ℝ :=
  ∑ u ∈ nodes N \ T, ∑ v ∈ T, cap G w u v

/-- The job set `I = T − {t}` of a sink side `T`. -/
def jobsOf {ι : Type*} [DecidableEq ι] (N : Finset ι) (T : Finset (Node ι)) : Finset ι :=
  N.filter (fun j => Node.job j ∈ T)

end LawlerWCT.RhoMax
