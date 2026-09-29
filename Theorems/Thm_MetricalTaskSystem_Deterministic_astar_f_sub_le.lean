import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 6.3** (Borodin–Linial–Saks 1992, p. 756). For the functions `f_k` of the algorithm
`A*_d`: `f_k(x) − f_k(y) ≤ d(y, x)` for all states `x, y` and all `k ≥ 0`. -/
theorem astar_f_sub_le {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) (x y : S) :
    fSeq d s k x - fSeq d s k y ≤ d y x := by sorry

end MetricalTaskSystem.Deterministic
