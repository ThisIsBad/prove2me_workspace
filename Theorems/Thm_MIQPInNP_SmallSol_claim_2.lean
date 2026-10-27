import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

open scoped Pointwise

/-- Claim 2, p. 8, restated with its context (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem claim_2 :
    ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      (∀ x ∈ cone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          x ≠ 0 → 0 < quadForm H x) →
      ∃ v : ℚ,
        bitSize v ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c
          + bitSize d) ∧
        ∀ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          quadVal H c d x ≤ 0 → euclidNorm x ≤ v := by sorry

end MIQPInNP.SmallSol

