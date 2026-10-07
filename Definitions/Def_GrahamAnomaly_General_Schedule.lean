import Mathlib

namespace GrahamAnomaly.General

/-- A feasible nonpreemptive execution of the tasks `Fin r` on `n` identical processors.
Task `j` occupies `[S j, S j + μ j)` on processor `P j`. -/
structure Schedule {r : ℕ} (n : ℕ) (μ : Fin r → ℝ)
    (prec : Fin r → Fin r → Prop) where
  S : Fin r → ℝ
  P : Fin r → Fin n
  nonneg : ∀ j, 0 ≤ S j
  noOverlap : ∀ i j, P i = P j → i ≠ j →
    S i + μ i ≤ S j ∨ S j + μ j ≤ S i
  precedence : ∀ i j, prec i j → S i + μ i ≤ S j

namespace Schedule

/-- The least time at which every task has completed, or zero for no tasks. -/
noncomputable def finish {r n : ℕ} {μ : Fin r → ℝ}
    {prec : Fin r → Fin r → Prop} (G : Schedule n μ prec) : ℝ :=
  if h : (Finset.univ : Finset (Fin r)).Nonempty then
    Finset.univ.sup' h (fun j => G.S j + μ j)
  else 0

end Schedule

end GrahamAnomaly.General
