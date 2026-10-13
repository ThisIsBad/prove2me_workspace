import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- §9, p. 666 (proof of Lemma 9.1, value identity). Let `G = (U, V, E)` be an `n`-by-`n`
bipartite graph and `l` any sequence of all the jobs `U ∪ V` of `S_G`. With `σ(i)` the number of
jobs of `V` scheduled before `i` jobs of `U` have been scheduled (`vBefore l i`), one has
`σ(n + 1) = n`, and the value of `l` is
`Σ_{i=1}^{n} (σ(i + 1) − σ(i)) · i = n² − Σ_{i=1}^{n} σ(i)`. -/
theorem value_identity {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n) (l : List (U ⊕ V))
    (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l) :
    vBefore l (n + 1) = n ∧
      valSG l = ∑ i ∈ Finset.Icc 1 n, ((vBefore l (i + 1) : ℝ) - (vBefore l i : ℝ)) * (i : ℝ) ∧
      valSG l = (n : ℝ) ^ 2 - ∑ i ∈ Finset.Icc 1 n, (vBefore l i : ℝ) := by sorry

end SingleMachinePrec.Biclique

