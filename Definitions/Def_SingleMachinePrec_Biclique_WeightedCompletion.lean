import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible

namespace SingleMachinePrec.Biclique

/-- The objective of `1 | prec | Σ w_j C_j` (Ambühl, Mastrolilli, Mutsanas, Svensson 2011, §1,
p. 653): the weighted sum of completion times `val(σ) = Σ_{j ∈ J} w_j C_j` of the sequence `l` of
the job set `J`. The machine processes the jobs of `l` one after another from time `0`, without
idle time or pre-emption, so `C_j` is the sum of the processing times `p` of the jobs of `l` up
to and including `j` (the published `MooreLateJobs.Shared.completionTime`). -/
noncomputable def weightedCompletion {ι : Type*} [DecidableEq ι] (p w : ι → ℝ) (J : Finset ι)
    (l : List ι) : ℝ :=
  ∑ j ∈ J, w j * MooreLateJobs.Shared.completionTime p l j

/-- `l` is an optimal schedule of `1 | prec | Σ w_j C_j` (§1, p. 653): a sequence of `J` that
observes the precedence constraints `prec` (the published `LawlerPrec.MinMax.IsFeasible`: `prec i j`
with `i ≠ j` forces `i` before `j`), whose weighted sum of completion times is at most that of
every such sequence. -/
def IsOptimalSchedule {ι : Type*} [DecidableEq ι] (prec : ι → ι → Prop) (p w : ι → ℝ)
    (J : Finset ι) (l : List ι) : Prop :=
  LawlerPrec.MinMax.IsFeasible prec J l ∧
    ∀ l' : List ι, LawlerPrec.MinMax.IsFeasible prec J l' →
      weightedCompletion p w J l ≤ weightedCompletion p w J l'

end SingleMachinePrec.Biclique
