import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

open scoped Pointwise

/-- Claim 1, p. 7, restated with its context (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem claim_1 :
    ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (i : Fin k),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      quadForm H (toReal (r i)) = 0 →
      (∃ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}),
          2 * (∑ u, ∑ v, x u * (H u v : ℝ) * toReal (r i) v) + ∑ u, (c u : ℝ) * toReal (r i) u
            < 0) →
      ∃ xt : Fin n → ℚ,
        toReal xt ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}) ∧
        2 * (∑ u, ∑ v, toReal xt u * (H u v : ℝ) * toReal (r i) v)
            + ∑ u, (c u : ℝ) * toReal (r i) u < 0 ∧
        vecSize xt ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c) := by sorry

end MIQPInNP.SmallSol

