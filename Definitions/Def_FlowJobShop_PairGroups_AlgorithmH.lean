import Mathlib
import Definitions.Def_FlowJobShop_PairGroups_FlowShop

namespace FlowJobShop.PairGroups

/-- The number of processors in group `g` (0-based) of an `m`-processor flow shop: group `g`
holds the processors `2g` and `2g + 1` (0-based) that exist, i.e. `min 2 (m − 2g)` of them. In
the paper's 1-based numbering, group `g + 1` holds `P_{2g+1}` and `P_{2g+2}`. -/
def groupSize (m : ℕ) (g : Fin ((m + 1) / 2)) : ℕ := min 2 (m - 2 * g.val)

/-- The `k`-th processor (0-based, `k < groupSize m g`) of group `g`: processor `2g + k`. -/
def groupProc {m : ℕ} (g : Fin ((m + 1) / 2)) (k : Fin (groupSize m g)) : Fin m :=
  ⟨2 * g.val + k.val, by have := k.isLt; unfold groupSize at this; omega⟩

/-- The group containing processor `j` (0-based): group `⌊j/2⌋`. -/
def groupOf {m : ℕ} (j : Fin m) : Fin ((m + 1) / 2) :=
  ⟨j.val / 2, by have := j.isLt; omega⟩

/-- The position of processor `j` inside its group: `j mod 2`. -/
def posInGroup {m : ℕ} (j : Fin m) : Fin (groupSize m (groupOf j)) :=
  ⟨j.val % 2, by have := j.isLt; unfold groupSize groupOf; simp only; omega⟩

namespace FlowShop

variable {m n : ℕ}

/-- The flow shop **on group `g`**: the same `n` jobs, with the processors of group `g` only
(`P_{2g+1}`, `P_{2g+2}` in the paper's 1-based numbering, or `P_m` alone for the last group
when `m` is odd), and task times `t_{2g+1,i}, t_{2g+2,i}`. Its first task has no predecessor. -/
def group (F : FlowShop m n) (g : Fin ((m + 1) / 2)) : FlowShop (groupSize m g) n where
  t k i := F.t (groupProc g k) i
  t_nonneg _ _ := F.t_nonneg _ _

/-- The offset of group `g` in algorithm H: `Σ_{h < g} FT(R(h))`, the total length of the
schedules of the groups before `g`. -/
noncomputable def offset (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ) (g : Fin ((m + 1) / 2)) :
    ℝ :=
  ∑ h ∈ (Finset.univ.filter (fun h : Fin ((m + 1) / 2) => h < g)), (F.group h).finishTime (R h)

/-- **Algorithm H** (p. 48), given schedules `R g` of the group flow shops: the `⌈m/2⌉` group
schedules are concatenated. A task on processor `j` of group `g` starts at its start time in
`R g` plus the offset `Σ_{h<g} FT(R(h))`. -/
noncomputable def algorithmH (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun j i => R (groupOf j) (posInGroup j) i + F.offset R (groupOf j)

end FlowShop

end FlowJobShop.PairGroups
