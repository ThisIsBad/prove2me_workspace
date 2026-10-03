import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.3, pp. 295–296: `f : M → M` exhibits sensitive dependence on initial conditions
if there is a `δ > 0` such that for any `x ∈ M` and any `ε > 0` there are a `y ∈ M` and an
`n ∈ ℕ = {1, 2, …}` with `d(x, y) < ε` and `d(fⁿ(x), fⁿ(y)) > δ`. -/
def SensitiveDependence {M : Type*} [MetricSpace M] (f : M → M) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : M, ∀ ε : ℝ, 0 < ε →
    ∃ y : M, ∃ n : ℕ, 1 ≤ n ∧ dist x y < ε ∧ δ < dist (f^[n] x) (f^[n] y)

end TeschlODE.IntervalMaps
