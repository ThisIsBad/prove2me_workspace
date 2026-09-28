import Mathlib

namespace IPProximity.Eisenbrand

/-- The set `{z ∈ ℤⁿ : A z = b, 0 ≤ z ≤ u}` of feasible integer solutions of the integer
program (10) of Eisenbrand–Weismantel (p. 5:7). -/
def ipFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (u : Fin n → ℕ) :
    Set (Fin n → ℤ) :=
  {z | Matrix.mulVec A z = b ∧ ∀ i, 0 ≤ z i ∧ z i ≤ (u i : ℤ)}

end IPProximity.Eisenbrand
