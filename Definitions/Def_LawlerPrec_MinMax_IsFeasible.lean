import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime

namespace LawlerPrec.MinMax

/-- A sequence of the job set `J` that observes the precedence constraints `prec`
(Lawler 1973, §1, p. 544): `prec i j` means that job `i` is required to precede job `j`.
The list `l` lists every job of `J` exactly once (`MooreLateJobs.Shared.IsSchedule`), and no job
appears before a job it is required to follow: whenever `x` comes before `y` in `l`,
`prec y x` fails. The relation `prec` is arbitrary (not assumed transitive, irreflexive or
acyclic); a cycle among distinct jobs of `J` leaves no feasible sequence. -/
def IsFeasible {ι : Type*} (prec : ι → ι → Prop) (J : Finset ι) (l : List ι) : Prop :=
  MooreLateJobs.Shared.IsSchedule J l ∧ l.Pairwise (fun x y => ¬ prec y x)

end LawlerPrec.MinMax
