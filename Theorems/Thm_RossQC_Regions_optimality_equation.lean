import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

open Filter Topology

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, §2, (1), p. 588 (unnumbered statement): "It is well known (see [1]) that
`V_β(P)` is the unique solution to (1)".

Under the standing hypotheses of §1–§2 (`Model.Valid`):

1. for every belief `P ∈ S` the value iterates `V^n(P)` converge (so `V_β(P)` is their limit);
2. `V_β` is bounded on `S`;
3. `V_β` satisfies the optimality equation (1) at every `P ∈ S`;
4. every function `W` that is bounded on `S` and satisfies (1) on `S` equals `V_β` on `S`.

**Formalization Note.** `V_β` is defined as the limit of value iteration from `V⁰ = 0`
(see `Model.Vβ`), not as an infimum over a policy class. Uniqueness is asserted in the class of
functions bounded on `S`, the setting of Blackwell [1]. The second half of the paper's sentence ("any
rule which … selects an action which minimizes the right side of (1) is β-optimal") is the convention
by which β-optimality is formalized elsewhere in this mission, not a claim of this theorem. -/
theorem optimality_equation {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid) :
    (∀ P ∈ M.simplex, ∃ L : ℝ, Tendsto (fun n => M.valueIter n P) atTop (𝓝 L)) ∧
    (∃ B : ℝ, ∀ P ∈ M.simplex, |M.Vβ P| ≤ B) ∧
    (∀ P ∈ M.simplex, M.Vβ P = M.bellman M.Vβ P) ∧
    (∀ W : (ι → ℝ) → ℝ, (∃ B : ℝ, ∀ P ∈ M.simplex, |W P| ≤ B) →
      (∀ P ∈ M.simplex, W P = M.bellman W P) → ∀ P ∈ M.simplex, W P = M.Vβ P) := by sorry

end RossQC.Regions

