import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- Lemma 9.1 (Ambühl, Mastrolilli, Mutsanas, Svensson 2011, p. 666). Let `G = (U, V, E)` be an
`n`-by-`n` bipartite graph and `S_G` its bipartite scheduling instance (jobs `U ∪ V`, precedence
constraints `P = (U × V) \ E`, the jobs of `U` with processing time `1` and weight `0`, the jobs of
`V` with processing time `0` and weight `1`). If a maximum edge biclique of `G` has value `a n²`
for some `a ∈ (0, 1]`, then an optimal schedule `σ*` of `S_G` exists, and every optimal schedule
satisfies `n² − a n² (ln (1/a) + 2) ≤ val(σ*) ≤ n² − a n²` (natural logarithm). -/
theorem lemma_9_1 {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2) :
    (∃ l : List (U ⊕ V), IsOptimalSG E l) ∧
      ∀ l : List (U ⊕ V), IsOptimalSG E l →
        (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 * (Real.log (1 / a) + 2) ≤ valSG l ∧
          valSG l ≤ (n : ℝ) ^ 2 - a * (n : ℝ) ^ 2 := by sorry

end SingleMachinePrec.Biclique

