import Mathlib

namespace ScenarioReduction.TernaryTree

/-- The reduction cost of eq. (8) of Heitsch–Römisch (2003): for scenarios indexed by a finite
type `ι` with probabilities `p` and cost `c`, deleting the index set `J` (whose complement is
nonempty) costs `D_J = Σ_{i ∈ J} p i · min_{j ∉ J} c i j`. -/
noncomputable def redCost {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (c : ι → ι → ℝ) (J : Finset ι) (hJ : Jᶜ.Nonempty) : ℝ :=
  ∑ i ∈ J, p i * Jᶜ.inf' hJ (fun j => c i j)

end ScenarioReduction.TernaryTree
