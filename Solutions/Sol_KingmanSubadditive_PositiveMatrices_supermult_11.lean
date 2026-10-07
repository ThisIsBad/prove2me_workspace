import Mathlib



namespace KingmanSubadditive.PositiveMatrices

theorem supermult_11_core {k : ℕ} [NeZero k] (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    A 0 0 * B 0 0 ≤ (A * B) 0 0 := by
  rw [Matrix.mul_apply]
  have := Finset.single_le_sum (f := fun l => A 0 l * B l 0)
    (fun l _ => le_of_lt (mul_pos (hA 0 l) (hB l 0))) (Finset.mem_univ (0 : Fin k))
  simpa using this

end KingmanSubadditive.PositiveMatrices

open KingmanSubadditive.PositiveMatrices


theorem solution {k : ℕ} [NeZero k] (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    A 0 0 * B 0 0 ≤ (A * B) 0 0 := by
  exact supermult_11_core A B hA hB
