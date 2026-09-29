import Mathlib

namespace LocalSearchFL.CFL

/-- A **metric instance** of the facility location problems (Arya et al. 2004, §2, pp. 546–547):
a set of clients `Cl`, a set of facilities `Fa`, and a distance `d` on the disjoint union
`Cl ⊕ Fa` that is nonnegative, symmetric and satisfies the triangle inequality. The distance is
defined between any two points (client–facility, client–client, facility–facility) because the
analysis of §5 uses facility–facility distances `c_{ss'}` and `c_{so}` and applies the triangle
inequality through clients. `d x x = 0` is not assumed. -/
structure MetricInstance (Cl Fa : Type) where
  /-- The distance between two points of `Cl ⊕ Fa`. -/
  d : Cl ⊕ Fa → Cl ⊕ Fa → ℝ
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The service cost `c_{ji}` of serving client `j` by (a copy of) facility `i`. -/
def MetricInstance.c {Cl Fa : Type} (I : MetricInstance Cl Fa) (j : Cl) (i : Fa) : ℝ :=
  I.d (Sum.inl j) (Sum.inr i)

/-- The distance `c_{ii'}` between two facilities. -/
def MetricInstance.cf {Cl Fa : Type} (I : MetricInstance Cl Fa) (i i' : Fa) : ℝ :=
  I.d (Sum.inr i) (Sum.inr i')

end LocalSearchFL.CFL
