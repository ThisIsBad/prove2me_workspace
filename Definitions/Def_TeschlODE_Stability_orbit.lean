import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.3, p. 192, (6.15): the orbit `γ(x) = Φ(I_x × {x})` of `x`. -/
def orbit {n : ℕ} (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun t => Φ t x) '' I x

end TeschlODE.Stability
