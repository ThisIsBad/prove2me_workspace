import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.2, p. 189: an integral curve (solution) of the autonomous system
`ẋ = f(x)` (6.7) in `M`, defined on the time set `J`. `J` is an open interval (open and
order-connected, possibly empty or unbounded), `φ` maps `J` into `M`, and `φ` has derivative
`f (φ t)` at every `t ∈ J`. Only the values of `φ` on `J` matter. -/
def IsIntegralCurve {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (J : Set ℝ) (φ : ℝ → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (∀ t ∈ J, φ t ∈ M) ∧ ∀ t ∈ J, HasDerivAt φ (f (φ t)) t

end TeschlODE.Stability
