import Mathlib
import Definitions.Def_ScenarioReduction_BinaryTree_scenario

namespace ScenarioReduction.BinaryTree

/-- The index set `I_*` of the proof of Proposition 3.1 (p. 197), stated by branch indices:
scenarios whose branch at level `k0` differs from the branch at level `k0 + 1`, and whose
branches at levels `k0 + 1` and `k0 + 2` agree. When `δ^{k0}, δ^{k0+1}, δ^{k0+2} > 0` this is
the paper's `{i : sign δ^{k0}_{i_{k0}} = -sign δ^{k0+1}_{i_{k0+1}} = -sign δ^{k0+2}_{i_{k0+2}}}`. -/
def IStar (K k0 : ℕ) : Finset (Fin K → Fin 2) :=
  Finset.univ.filter (fun σ => lev σ k0 ≠ lev σ (k0 + 1) ∧ lev σ (k0 + 1) = lev σ (k0 + 2))

end ScenarioReduction.BinaryTree
