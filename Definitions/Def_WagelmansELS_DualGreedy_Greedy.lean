import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Model

namespace WagelmansELS.DualGreedy

/-- Use of constraint `i` before period `j`; the interval is empty at `i = j`. -/
def pastUse (P : Instance) (v : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico i j, P.d t * max 0 (v t - P.c i)

/-- The upper bound on `v_j` given by constraint `i`, when `d_j > 0`. -/
noncomputable def greedyBound (P : Instance) (v : ℕ → ℝ) (i j : ℕ) : ℝ :=
  P.c i + (P.f i - pastUse P v i j) / P.d j

/-- The greedy forward rule at each positive-demand period. Zero-demand coordinates are free. -/
def IsGreedyForward (P : Instance) (v : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (hj1 : 1 ≤ j) (_hjn : j ≤ P.n) (_hdj : 0 < P.d j),
    v j = (Finset.Icc 1 j).inf' (by
      refine ⟨1, Finset.mem_Icc.mpr ?_⟩
      exact ⟨le_refl _, hj1⟩) (fun i => greedyBound P v i j)

/-- One choice of greedy forward solution; zero-demand coordinates are set to zero. -/
noncomputable def greedy (P : Instance) (j : ℕ) : ℝ :=
  (Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => (0 : ℝ)) (fun k hist =>
    fun t => if t = k + 1 then
      if k + 1 ≤ P.n ∧ 0 < P.d (k + 1) then
        (Finset.Icc 1 (k + 1)).inf' (by
          refine ⟨1, Finset.mem_Icc.mpr ?_⟩
          omega) (fun i => greedyBound P hist i (k + 1))
      else 0
    else hist t) j) j

end WagelmansELS.DualGreedy
