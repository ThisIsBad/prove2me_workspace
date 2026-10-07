import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition

namespace FlowJobShop.ThreePartFlow

open ResourceScheduling.Chain

/-- The `s + t + 2` jobs of the flow shop `FS` built in the proof of Lemma 4
(Gonzalez–Sahni 1978, p. 41), with `s = 3t`. The paper numbers them `1, …, s + t + 2`:
* `elem i` is job `i + 1`, for `i = 0, …, s − 1` (the paper's jobs `1, …, s`);
* `first` is job `s + 1`;
* `middle k` is job `s + k + 2`, for `k = 0, …, t − 3` (the paper's jobs `s + i + 1`,
  `1 ≤ i ≤ t − 2`; there are exactly `t − 2` of them when `t ≥ 2`);
* `last` is job `s + t`;
* `tail3` is job `s + t + 1`;
* `tail1` is job `s + t + 2`.
The construction is meant for `t ≥ 2`; for `t < 2` the paper's indices `s + 1` and `s + t`
collide, and every theorem about this instance assumes `2 ≤ t`. -/
inductive FSJob (t : ℕ) where
  | elem (i : Fin (3 * t))
  | first
  | middle (k : Fin (t - 2))
  | last
  | tail3
  | tail1
  deriving DecidableEq, Fintype

/-- The task times of the flow shop `FS` of Lemma 4 (p. 41), processors `P_1, P_2, P_3` being
`0, 1, 2`, for a 3-Partition instance `C = (a_1, …, a_s, B)` (`C.b = B`):
* `t_{1,i} = t_{3,i} = a_i`, `t_{2,i} = 0` for `1 ≤ i ≤ s`;
* `t_{1,s+1} = 0`, `t_{2,s+1} = 2B`, `t_{3,s+1} = B`;
* `t_{1,s+i+1} = t_{3,s+i+1} = B`, `t_{2,s+i+1} = 2B` for `1 ≤ i ≤ t − 2`;
* `t_{1,s+t} = B`, `t_{2,s+t} = 2B`, `t_{3,s+t} = 0`;
* `t_{1,s+t+1} = t_{2,s+t+1} = 0`, `t_{3,s+t+1} = B`;
* `t_{1,s+t+2} = B`, `t_{2,s+t+2} = t_{3,s+t+2} = 0`. -/
noncomputable def fsTime (C : ThreePartition) : Fin 3 → FSJob C.t → ℝ
  | j, .elem i => ![(C.a i : ℝ), 0, (C.a i : ℝ)] j
  | j, .first => ![0, 2 * (C.b : ℝ), (C.b : ℝ)] j
  | j, .middle _ => ![(C.b : ℝ), 2 * (C.b : ℝ), (C.b : ℝ)] j
  | j, .last => ![(C.b : ℝ), 2 * (C.b : ℝ), 0] j
  | j, .tail3 => ![0, 0, (C.b : ℝ)] j
  | j, .tail1 => ![(C.b : ℝ), 0, 0] j

/-- The three-processor flow shop `FS` constructed from the 3-Partition instance `C` in the
proof of Lemma 4 (p. 41). -/
noncomputable def FS (C : ThreePartition) : FlowShop 3 (FSJob C.t) where
  m_pos := by omega
  t := fsTime C
  t_nonneg := by
    intro j i
    cases i <;> fin_cases j <;> simp [fsTime]

/-- The finish-time threshold `τ = 2tB` of Lemma 4. -/
noncomputable def tau (C : ThreePartition) : ℝ := 2 * (C.t : ℝ) * (C.b : ℝ)

end FlowJobShop.ThreePartFlow
