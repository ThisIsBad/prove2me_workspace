import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box

namespace LewisTorczon.BoundPS

/-- The stationarity measure `q(x) = P(x − g(x)) − x` of §3, p. 5, where `g = ∇f` is Mathlib's
`gradient f` (which is `0` where `f` is not differentiable; the theorems assume `f` is `C¹` on an
open set containing `Ω`, so there it is the true gradient). -/
noncomputable def projQ {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  boxProj lo hi (x - gradient f x) - x

/-- A stationary point of problem (1) (p. 1): a feasible `x` with `⟨∇f(x), z − x⟩ ≥ 0` for every
feasible `z`. -/
def IsStationary {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ box lo hi ∧ ∀ z ∈ box lo hi, 0 ≤ inner ℝ (gradient f x) (z - x)

end LewisTorczon.BoundPS
