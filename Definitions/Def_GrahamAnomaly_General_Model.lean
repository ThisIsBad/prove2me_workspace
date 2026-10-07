import Mathlib
import Definitions.Def_GrahamAnomaly_General_Schedule

namespace GrahamAnomaly.General

/-- Task `j` is ready at time `t` when all its predecessors have completed. -/
def IsReady {r n : ℕ} {μ : Fin r → ℝ}
    {prec : Fin r → Fin r → Prop} (G : Schedule n μ prec)
    (j : Fin r) (t : ℝ) : Prop :=
  ∀ i, prec i j → G.S i + μ i ≤ t

/-- Every processor executes a task at time `t`. -/
def AllBusy {r n : ℕ} {μ : Fin r → ℝ}
    {prec : Fin r → Fin r → Prop} (G : Schedule n μ prec) (t : ℝ) : Prop :=
  ∀ p : Fin n, ∃ k : Fin r, G.P k = p ∧ G.S k ≤ t ∧ t < G.S k + μ k

/-- Graham's list-scheduling rule: a ready task waiting to start never sees an idle
processor, and a task started while another ready task waits is earlier in `L`. -/
def IsListSchedule {r n : ℕ} {μ : Fin r → ℝ}
    {prec : Fin r → Fin r → Prop} (L : Fin r ≃ Fin r)
    (G : Schedule n μ prec) : Prop :=
  (∀ j t, 0 ≤ t → t < G.S j → IsReady G j t → AllBusy G t) ∧
  (∀ l j, G.S l < G.S j → IsReady G j (G.S l) →
    L.symm l < L.symm j)

end GrahamAnomaly.General
