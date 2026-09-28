import Mathlib

namespace LogRegretOCO.EWOO

/-- The set of "nearby points" in the proof of Theorem 7 (Hazan–Agarwal–Kale 2007, §3.4,
p. 187): `S = {T/(T+1) x* + 1/(T+1) y : y ∈ P}`, the image of `P` under the homothety with
centre `x*` and ratio `1/(T+1)`. -/
def shrunkSet {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (xstar : EuclideanSpace ℝ (Fin n))
    (T : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ y ∈ P, x = ((T : ℝ) / ((T : ℝ) + 1)) • xstar + (1 / ((T : ℝ) + 1)) • y}

end LogRegretOCO.EWOO
