import Definitions.Def_WilliamsonShmoys_SetCoverFrequency
import Mathlib.Order.Filter.Extr

set_option autoImplicit false
open scoped BigOperators
namespace WilliamsonShmoys

/-- Total processing time assigned to a machine: the equivalent load-balancing
model of §2.3, manuscript pp.39–40. An assignment processes every job exactly once. -/
noncomputable def machineLoad {n m : ℕ} (p : Fin n → ℝ)
    (assignment : Fin n → Fin m) (machine : Fin m) : ℝ :=
  ∑ j : Fin n, if assignment j = machine then p j else 0

/-- Maximum machine load; the branch for no machines only makes the definition
 total. The main statement explicitly requires a positive number of machines. -/
noncomputable def makespan {n m : ℕ} (p : Fin n → ℝ)
    (assignment : Fin n → Fin m) : ℝ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then
    Finset.univ.sup' h (machineLoad p assignment)
  else 0

/-- The positive integer instances of §3.2, manuscript p.69. Predecessors
encode positive processing times and a positive, variable machine count.
The empty job list is also allowed, with makespan zero. -/
structure ParallelPTASInput where
  machinesPred : ℕ
  processingPred : List ℕ

/-- Exact integral processing requirements, embedded into the existing
real-valued identical-machine objective. No rounding is part of the instance. -/
def parallelPTASTimes (I : ParallelPTASInput)
    (j : Fin I.processingPred.length) : ℝ :=
  ((I.processingPred.get j + 1 : ℕ) : ℝ)

/-- Binary positive machine count followed by binary positive job times,
using the existing comma-delimited encoder. No unary padding or solution data. -/
def parallelPTASEncodeInput (I : ParallelPTASInput) : List Computability.Γ' :=
  lptEncodeNaturals ((I.machinesPred + 1) :: I.processingPred.map (· + 1))

end WilliamsonShmoys
