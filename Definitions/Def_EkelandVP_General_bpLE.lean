import Mathlib

namespace EkelandVP.General

/-- The Bishop–Phelps order (1.6) of Ekeland (1974), p. 325, on `V × ℝ`:
`bpLE α (v₁, a₁) (v₂, a₂)` means `(v₁, a₁) ≺ (v₂, a₂)`, i.e. `(a₂ − a₁) + α d(v₁, v₂) ≤ 0`. -/
def bpLE {V : Type*} [MetricSpace V] (α : ℝ) (p q : V × ℝ) : Prop :=
  (q.2 - p.2) + α * dist p.1 q.1 ≤ 0

end EkelandVP.General
