import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_ThreeMachine
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine

namespace IgnallSchrage.Invariance

/-- p. 411 ("Define new time units"): multiplying all processing times by `H > 0` multiplies the
makespan and the sum of completion times of every sequence, and `T̂_r`, `Ŝ_r`, both lower
bounds of every node, by `H`. -/
theorem scale {n : ℕ} (a b c : Fin n → ℝ) (H : ℝ) (hH : 0 < H) :
    (∀ σ : Equiv.Perm (Fin n),
      IgnallSchrage.Makespan.makespan (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) σ =
        H * IgnallSchrage.Makespan.makespan a b c σ) ∧
    (∀ σ : Equiv.Perm (Fin n),
      sumCompletion (fun i => H * a i) (fun i => H * b i) σ = H * sumCompletion a b σ) ∧
    (∀ J : List (Fin n),
      lowerBound3 (fun i => H * a i) (fun i => H * b i) (fun i => H * c i) J =
        H * lowerBound3 a b c J) ∧
    (∀ J : List (Fin n),
      That (fun i => H * a i) (fun i => H * b i) J = H * That a b J ∧
      Shat (fun i => H * a i) (fun i => H * b i) J = H * Shat a b J ∧
      lowerBound2 (fun i => H * a i) (fun i => H * b i) J = H * lowerBound2 a b J) := by sorry

end IgnallSchrage.Invariance

