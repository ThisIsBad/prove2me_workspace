import Mathlib
import Definitions.Def_UnrelatedSched_FixedMachines_LongAssignment
import Definitions.Def_UnrelatedSched_FixedMachines_BinarySearch

namespace UnrelatedSched.FixedMachines

/-- §3, p. 6: for every LP solver (vertex selector) `V`, the procedure `A_ε` run with `V` exists
(every vertex of a feasible residual LP can be rounded), and every procedure that is `A_ε` run
with `V` is a `(1 + ε)`-relaxed decision procedure: it either answers 'no', in which case no
schedule has makespan at most `d`, or produces a schedule with makespan at most `(1 + ε) d`. -/
theorem relaxed_procedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (hP : ∀ i j, 0 < P i j) (ε : ℝ) (hε : 0 < ε)
    (V : ℕ → (Fin n → Option (Fin m)) → Option (Matrix (Fin m) (Fin n) ℝ))
    (hV : IsVertexSelector P ε V) :
    (∃ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D) ∧
    ∀ D : ℕ → Option (Fin n → Fin m), IsAepsProcedure P ε V D →
      IsRelaxedDecisionProcedure P (1 + ε) D := by sorry

end UnrelatedSched.FixedMachines

