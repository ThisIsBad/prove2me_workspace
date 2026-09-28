import Mathlib

namespace LogRegretOCO.EWOO

/-- α-exp-concavity on `P` (Hazan–Agarwal–Kale 2007, §2.2, p. 173): the function
`x ↦ exp(-α g(x))` is concave on `P`. The positivity `α > 0` of the paper's definition is a
separate hypothesis wherever this predicate is used. -/
def IsExpConcave {n : ℕ} (α : ℝ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ConcaveOn ℝ P (fun x => Real.exp (-α * g x))

end LogRegretOCO.EWOO
