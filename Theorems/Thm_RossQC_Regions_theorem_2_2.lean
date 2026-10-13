import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 589, Theorem 2.2: "Both the β-optimal inspect and revise regions are
convex."

Under the standing hypotheses of §1–§2 (`Model.Valid`), the β-optimal inspect region and the
β-optimal revise region (Definition, p. 588: the beliefs `P ∈ S` at which inspecting, resp.
revising, attains the minimum in (1)) are convex subsets of `ι → ℝ`.

**Formalization Note.** The regions are subsets of the state space `S` (`Model.region`), as the
paper's `{P : …}` ranges over `S`. `V_β` is the limit of value iteration (`Model.Vβ`). -/
theorem theorem_2_2 {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid) :
    Convex ℝ M.inspectRegion ∧ Convex ℝ M.reviseRegion := by sorry

end RossQC.Regions

