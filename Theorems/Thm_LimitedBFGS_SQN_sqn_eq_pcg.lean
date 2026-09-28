import Mathlib
import Definitions.Def_LimitedBFGS_SQN_sqnIter
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN

/-- Section 3, p. 778: on a strictly convex quadratic with exact line searches and `m ≥ 1`, the
SQN (17) is identical to the PCG with fixed preconditioner `H₀`: the iterates and the search
directions coincide at every step. -/
theorem sqn_eq_pcg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m)
    (x₀ : Fin n → ℝ) (i : ℕ) :
    (sqnIter A b H₀ m x₀ i).x = (pcgIter A b H₀ x₀ i).x ∧
      sqnDir A b H₀ (sqnIter A b H₀ m x₀ i) = (pcgIter A b H₀ x₀ i).d := by sorry

end LimitedBFGS.SQN

