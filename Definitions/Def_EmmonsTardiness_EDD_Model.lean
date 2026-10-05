import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

namespace EmmonsTardiness.EDD

open MooreLateJobs

/-- The objective `Σ_J g(T_i)` of p. 713: the sum over the job set `J` of the common loss
function `g` applied to each job's tardiness `EmmonsTardiness.SPT.tardiness p d l i` in the
sequence `l`. With `g = id` it is the total tardiness `T = Σ_J T_i` of p. 701. -/
noncomputable def totalPenalty {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ)
    (J : Finset ι) (l : List ι) : ℝ :=
  ∑ i ∈ J, g (EmmonsTardiness.SPT.tardiness p d l i)

/-- `l` is an optimal schedule of `J` for the objective `Σ_J g(T_i)`: it is a schedule of `J`
and no schedule of `J` has a smaller objective value. -/
def IsOptimal {ι : Type*} [DecidableEq ι] (g : ℝ → ℝ) (p d : ι → ℝ) (J : Finset ι)
    (l : List ι) : Prop :=
  Shared.IsSchedule J l ∧
    ∀ l' : List ι, Shared.IsSchedule J l' → totalPenalty g p d J l ≤ totalPenalty g p d J l'

/-- The waiting (or starting) time `W_i = C_i - p_i` of job `i` in the sequence `l`
(p. 706, Corollary 2.2). -/
noncomputable def startTime {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (l : List ι) (i : ι) : ℝ :=
  Shared.completionTime p l i - p i

/-- The sequence `l` is in EDD (earliest due date) order: due dates are nondecreasing along `l`.
Ties between equal due dates may be broken arbitrarily. -/
def IsEDDOrder {ι : Type*} (d : ι → ℝ) (l : List ι) : Prop :=
  l.Pairwise (fun a b => d a ≤ d b)

end EmmonsTardiness.EDD
