import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_VertexCoverGraph
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout

namespace SingleMachinePrec.IntervalReduction

variable {N : ℕ} {G : SimpleGraph (Fin N)}

/-- The number `i` of the vertex `v_i` (vertices are numbered `1, …, N`; `i : Fin N` is `v_{i+1}`). -/
def num (i : Fin N) : ℕ := i.val + 1

/-- The number of the parent of `v_j` in `T`, and `0` for the root `v_1` (so that the job `s_0`
plays the parent of `s_1` in the table on p. 662). -/
def parNum (L : TreeLayout G) (j : Fin N) : ℕ :=
  match L.par j with
  | none => 0
  | some i => i.val + 1

/-- The jobs of the scheduling instance `S` of Stage 2 (table, p. 662): `s_0`, the jobs `s_j`
(`j = 1, …, |V|`), `m_i` and `e_i` (`i = 1, …, |V|`), and `b_{ij}` for each
`{v_i, v_j} ∈ E \ E_T` with `i < j`. -/
inductive Job (L : TreeLayout G) : Type
  | s0
  | s (j : Fin N)
  | m (i : Fin N)
  | e (i : Fin N)
  | b (q : NonTreeEdge L)
  deriving DecidableEq

/-- The jobs as a sum type, used only to count them. -/
def Job.equivSum (L : TreeLayout G) : Job L ≃ Unit ⊕ Fin N ⊕ Fin N ⊕ Fin N ⊕ NonTreeEdge L where
  toFun
    | .s0 => .inl ()
    | .s j => .inr (.inl j)
    | .m i => .inr (.inr (.inl i))
    | .e i => .inr (.inr (.inr (.inl i)))
    | .b q => .inr (.inr (.inr (.inr q)))
  invFun
    | .inl () => .s0
    | .inr (.inl j) => .s j
    | .inr (.inr (.inl i)) => .m i
    | .inr (.inr (.inr (.inl i))) => .e i
    | .inr (.inr (.inr (.inr q))) => .b q
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟩ | x | x | x | x <;> rfl

noncomputable instance Job.instFintype (L : TreeLayout G) : Fintype (Job L) :=
  Fintype.ofEquiv _ (Job.equivSum L).symm

/-- Left end `a_x` of the interval representation of job `x` (table, p. 662):
`s_0 ↦ −1`, `s_j ↦ i` with `v_i` the parent of `v_j` (`0` for `s_1`), `m_i ↦ i − 1/2`,
`e_i ↦ |V| + i`, `b_{ij} ↦ i`. -/
noncomputable def left (L : TreeLayout G) : Job L → ℝ
  | .s0 => -1
  | .s j => (parNum L j : ℝ)
  | .m i => (num i : ℝ) - 1 / 2
  | .e i => (N : ℝ) + num i
  | .b q => (num q.1.1 : ℝ)

/-- Right end `b_x` of the interval representation of job `x` (table, p. 662):
`s_0 ↦ 0`, `s_j ↦ j`, `m_i ↦ |V| + i`, `e_i ↦ |V| + i + 1`, `b_{ij} ↦ j − 1/2`. -/
noncomputable def right (L : TreeLayout G) : Job L → ℝ
  | .s0 => 0
  | .s j => (num j : ℝ)
  | .m i => (N : ℝ) + num i
  | .e i => (N : ℝ) + num i + 1
  | .b q => (num q.1.2 : ℝ) - 1 / 2

/-- Every interval of the table is a genuine closed interval `[a_x, b_x]` with `a_x ≤ b_x`. -/
theorem left_le_right (L : TreeLayout G) (x : Job L) : left L x ≤ right L x := by
  cases x with
  | s0 => norm_num [left, right]
  | s j =>
    simp only [left, right, parNum, num]
    cases h : L.par j with
    | none => simp; positivity
    | some i =>
      have := L.par_lt j i h
      simp only
      exact_mod_cast Nat.succ_le_succ (Fin.le_iff_val_le_val.mp this.le)
  | m i => simp only [left, right]; have : (0 : ℝ) ≤ N := by positivity
           linarith
  | e i => simp only [left, right]; linarith
  | b q =>
    simp only [left, right, num]
    have h : q.1.1.val + 1 ≤ q.1.2.val := q.2.1
    have h' : ((q.1.1.val + 1 : ℕ) : ℝ) ≤ (q.1.2.val : ℝ) := by exact_mod_cast h
    push_cast at h' ⊢
    linarith

/-- The precedence constraints `I` of `S` (p. 662): the interval order of the table's intervals,
`x ≤ y` iff `x = y` or `b_x < a_y` (the interval of `x` lies strictly to the left of that of `y`). -/
noncomputable instance Job.instPartialOrder (L : TreeLayout G) : PartialOrder (Job L) where
  le x y := x = y ∨ right L x < left L y
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | h
    · exact hyz
    · rcases hyz with rfl | h'
      · exact Or.inr h
      · exact Or.inr (by linarith [left_le_right L y])
  le_antisymm x y hxy hyx := by
    rcases hxy with h | h
    · exact h
    · rcases hyx with h' | h'
      · exact h'.symm
      · exact absurd h (by linarith [left_le_right L x, left_le_right L y])

/-- The precedence relation `I` as a relation (`(x, y) ∈ I` iff `x ≤ y` in the interval order). -/
def prec (L : TreeLayout G) (x y : Job L) : Prop := x ≤ y

/-- Processing times of `S` (table, p. 662), for the parameter `k`: `p(s_0) = 1`,
`p(s_j) = 1/k^j`, `p(m_i) = 1/k^{|V|+i}`, `p(e_i) = 0`, `p(b_{ij}) = 1/k^j`. -/
noncomputable def procTime (L : TreeLayout G) (k : ℝ) : Job L → ℝ
  | .s0 => 1
  | .s j => 1 / k ^ num j
  | .m i => 1 / k ^ (N + num i)
  | .e _ => 0
  | .b q => 1 / k ^ num q.1.2

/-- Weights of `S` (table, p. 662), for the parameter `k`: `w(s_0) = 0`, `w(s_j) = k^i` with
`v_i` the parent of `v_j` (`w(s_1) = 1`), `w(m_i) = k^i`, `w(e_i) = k^{|V|+i}`,
`w(b_{ij}) = k^i`. -/
noncomputable def weight (L : TreeLayout G) (k : ℝ) : Job L → ℝ
  | .s0 => 0
  | .s j => k ^ parNum L j
  | .m i => k ^ num i
  | .e i => k ^ (N + num i)
  | .b q => k ^ num q.1.1

/-- The number `n` of jobs of `S`. -/
noncomputable def numJobs (L : TreeLayout G) : ℕ := Fintype.card (Job L)

/-- The value `k = n² + 1` fixed at the end of the proof of Theorem 7.1 (p. 664). -/
noncomputable def kVal (L : TreeLayout G) : ℝ := (numJobs L : ℝ) ^ 2 + 1

/-- Membership in the set `D` of pairs (p. 663):
`D = {(s_0, s_1)} ∪ {(s_i, s_j) : v_i parent of v_j in T} ∪ {(s_i, m_i), (m_i, e_i)}
∪ {(s_i, b_{ij}), (b_{ij}, m_j) : {v_i, v_j} ∈ E \ E_T, i < j}`. -/
def InD (L : TreeLayout G) : Job L → Job L → Prop
  | .s0, .s j => L.par j = none
  | .s i, .s j => L.par j = some i
  | .s i, .m i' => i = i'
  | .m i, .e i' => i = i'
  | .s i, .b q => q.1.1 = i
  | .b q, .m j => q.1.2 = j
  | _, _ => False

/-- The vertex cover graph `G^S_I` of the instance `S` (§2.2, p. 656). -/
def GSI (L : TreeLayout G) : SimpleGraph (IncPair (prec L)) :=
  vertexCoverGraph (prec L)

/-- The subgraph `G′_I = (D, E_I)` of `G^S_I` induced by the incomparable pairs in `D` (p. 663). -/
def GIprime (L : TreeLayout G) : SimpleGraph {u : IncPair (prec L) | InD L u.1.1 u.1.2} :=
  (GSI L).induce {u : IncPair (prec L) | InD L u.1.1 u.1.2}

/-- `w(C_I)`: the minimum weight of a vertex cover of `G^S_I` with node weights `p_i w_j`, for the
instance `S` with `k = n² + 1` (p. 664). -/
noncomputable def tauW (L : TreeLayout G) : ℝ :=
  minWeightVC (prec L) (procTime L (kVal L)) (weight L (kVal L))

end SingleMachinePrec.IntervalReduction
