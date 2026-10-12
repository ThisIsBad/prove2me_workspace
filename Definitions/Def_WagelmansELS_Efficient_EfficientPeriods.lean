import Mathlib
import Definitions.Def_WagelmansELS_Efficient_Instance

namespace WagelmansELS.Efficient
namespace Instance
variable (P : Instance)

/-- A breakpoint of the lower convex envelope of `(D t,G t)`, represented by
its earliest period at equal abscissa and height. Collinear interior points are excluded. -/
def IsEfficient (i t : ℕ) : Prop :=
  t ∈ Finset.Ioc i (P.n + 1) ∧
  (∀ u ∈ Finset.Ioc i (P.n + 1), u ≠ t → P.D u = P.D t →
    P.G t < P.G u ∨ (P.G t = P.G u ∧ t < u)) ∧
  ¬ ∃ u ∈ Finset.Ioc i (P.n + 1), ∃ w ∈ Finset.Ioc i (P.n + 1),
    P.D u < P.D t ∧ P.D t < P.D w ∧
    (P.D w - P.D u) * P.G t ≥
      (P.D w - P.D t) * P.G u + (P.D t - P.D u) * P.G w

/-- The efficient periods for iteration `i`. -/
noncomputable def E (i : ℕ) : Finset ℕ :=
  by
  classical
  exact (Finset.Ioc i (P.n + 1)).filter (P.IsEfficient i)

end Instance
end WagelmansELS.Efficient
