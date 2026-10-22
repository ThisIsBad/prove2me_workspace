import Mathlib

namespace FriezeKannan.PseudoReg

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `M(S, T) = ∑_{i ∈ S} ∑_{j ∈ T} M i j` (§2.1, p. 178). -/
def blockSum (M : Matrix V V ℝ) (S T : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, M i j

/-- The Frobenius norm `‖M‖_F = (∑_{i,j} M i j ^ 2)^{1/2}` (§2.1, p. 177). -/
noncomputable def frobNorm (M : Matrix V V ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The cut matrix `CUT(S, T, d)`: entry `d` on `S × T`, `0` elsewhere (§2.1, p. 178). -/
def cutMatrix (S T : Finset V) (d : ℝ) : Matrix V V ℝ :=
  fun i j => if i ∈ S ∧ j ∈ T then d else 0

/-- The sum `D = D⁽¹⁾ + ⋯ + D⁽ˢ⁾` of the cut matrices `CUT(R_t, C_t, d_t)`, `t = 1, …, s`. -/
def cutSum {s : ℕ} (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ) : Matrix V V ℝ :=
  ∑ t, cutMatrix (Rs t) (Cs t) (d t)

/-- `Δ_P(S, T) = e(S, T) − ∑_{i ∈ K} ∑_{j ∈ K} d_{i,j} |S_i| |T_j|` (§5.1, p. 203), where the
parts `V_i` of `P` index the sums, `S_i = S ∩ V_i`, `T_j = T ∩ V_j`, and
`d_{i,j} = G.edgeDensity V_i V_j` is the number of ordered adjacent pairs in `V_i × V_j`
divided by `|V_i| |V_j|` (for `i = j` this is the block average `2 e(V_i) / |V_i|²`). -/
noncomputable def delta (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V)) (S T : Finset V) : ℝ :=
  ((G.interedges S T).card : ℝ) -
    ∑ Vi ∈ P.parts, ∑ Vj ∈ P.parts,
      (G.edgeDensity Vi Vj : ℝ) * ((S ∩ Vi).card : ℝ) * ((T ∩ Vj).card : ℝ)

/-- A partition `P` of `V` is `ε`-pseudo-regular if `|Δ_P(S, T)| ≤ ε n²` for all disjoint
`S, T ⊆ V`, where `n = |V|` (§5.1, p. 203). -/
def IsPseudoRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V)) (ε : ℝ) : Prop :=
  ∀ S T : Finset V, Disjoint S T → |delta G P S T| ≤ ε * (Fintype.card V : ℝ) ^ 2

/-- The block-average matrix `M_Q`: `M_Q(p, q) = M(W_i, W_j) / (|W_i| |W_j|)` for
`(p, q) ∈ W_i × W_j`, where `W_i = Q.part p` and `W_j = Q.part q` (§5.1, p. 203). -/
noncomputable def blockAvg (Q : Finpartition (Finset.univ : Finset V)) (M : Matrix V V ℝ) :
    Matrix V V ℝ :=
  fun p q => blockSum M (Q.part p) (Q.part q) /
    (((Q.part p).card : ℝ) * ((Q.part q).card : ℝ))

/-- A matrix `M` is compatible with the partition `Q` if `M(p, q)` is constant over every block
`W_i × W_j` of parts of `Q` (§5.1, p. 203). -/
def Compatible (Q : Finpartition (Finset.univ : Finset V)) (M : Matrix V V ℝ) : Prop :=
  ∀ p p' q q' : V, Q.part p = Q.part p' → Q.part q = Q.part q' → M p q = M p' q'

/-- The coarsest partition of `V` in which every `R_t` and every `C_t` is a union of parts:
the nonempty atoms of the family `{R_1, …, R_s, C_1, …, C_s}` (§5.1, p. 204). -/
def atomPartition {s : ℕ} (Rs Cs : Fin s → Finset V) : Finpartition (Finset.univ : Finset V) :=
  Finpartition.atomise Finset.univ (Finset.univ.image Rs ∪ Finset.univ.image Cs)

end FriezeKannan.PseudoReg
