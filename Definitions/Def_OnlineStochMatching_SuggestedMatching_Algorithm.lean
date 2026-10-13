import Definitions.Def_OnlineStochMatching_SuggestedMatching_Instance
import Definitions.Def_OnlineStochMatching_SuggestedMatching_BallsInBins

namespace OnlineStochMatching.SuggestedMatching

variable {A I : Type} [Fintype A] [Fintype I]

/-- The suggested matching algorithm's output: each labelled advertiser is assigned
on its first selection, so the output is the number of distinct selected ads. -/
noncomputable def algorithm (inst : Instance A I) (label : inst.Copy → Option A)
    (ω : Fin inst.n → inst.Copy) : ℕ := by
  classical
  exact (Finset.univ.filter fun a : A => ∃ t, label (ω t) = some a).card

/-- Probability of an event under independent uniform copy draws. -/
noncomputable def runProbability (inst : Instance A I)
    (P : (Fin inst.n → inst.Copy) → Prop) : ℝ := uniformProbability P

/-- Expected number of assignments by the suggested matching algorithm. -/
noncomputable def expectedAlgorithm (inst : Instance A I) (label : inst.Copy → Option A) : ℝ :=
  uniformExpectation (fun ω : Fin inst.n → inst.Copy => (algorithm inst label ω : ℝ))

/-- The complete bipartite instance with `n` advertisers, `n` types, and `e_i = 1`. -/
def completeInstance (n : ℕ) (hn : 0 < n) : Instance (Fin n) (Fin n) where
  E := Finset.univ
  e := fun _ => 1
  n := n
  n_eq := by simp
  n_pos := hn

end OnlineStochMatching.SuggestedMatching
