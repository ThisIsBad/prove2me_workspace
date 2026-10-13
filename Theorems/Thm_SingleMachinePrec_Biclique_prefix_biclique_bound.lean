import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- §9, p. 666 (proof of Lemma 9.1, per-prefix bound). Let `G = (U, V, E)` be an `n`-by-`n`
bipartite graph whose maximum edge biclique has value `a n²`, and let `l` be a feasible schedule
of `S_G` (a sequence of all the jobs observing `P = (U × V) \ E`). With `σ(i)` the number of jobs
of `V` scheduled before `i` jobs of `U` have been scheduled, for every `i = 1, …, n`,
`σ(i) (n − i + 1) ≤ a n²` and `σ(i) ≤ n`. -/
theorem prefix_biclique_bound {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U]
    [DecidableEq V] (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n)
    (hV : Fintype.card V = n) (a : ℝ) (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2)
    (l : List (U ⊕ V)) (hl : LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (vBefore l i : ℝ) * ((n : ℝ) - (i : ℝ) + 1) ≤ a * (n : ℝ) ^ 2 ∧ vBefore l i ≤ n := by sorry

end SingleMachinePrec.Biclique

