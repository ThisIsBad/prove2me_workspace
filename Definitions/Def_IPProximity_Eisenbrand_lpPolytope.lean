import Mathlib

namespace IPProximity.Eisenbrand

/-- The feasible region `{x ∈ ℝⁿ : A x = b, 0 ≤ x ≤ u}` of the linear programming relaxation of
the integer program (10) of Eisenbrand–Weismantel (p. 5:7); the integral data `A, b, u` are cast
to `ℝ`. -/
def lpPolytope {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (u : Fin n → ℕ) :
    Set (Fin n → ℝ) :=
  {x | Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) x = (fun i => (b i : ℝ)) ∧
    ∀ i, 0 ≤ x i ∧ x i ≤ (u i : ℝ)}

end IPProximity.Eisenbrand
