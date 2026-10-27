import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

/-- Lemma 6 (normalizing hyperplane), p. 5 (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem lemma_6 :
    ∃ g : Polynomial ℕ, ∀ (n s : ℕ) (r : Fin s → Fin n → ℚ) (hs : 0 < s),
      IsPointedCone (cone (Set.range fun i => toReal (r i))) →
      ∃ f : Fin n → ℚ,
        vecSize f ≤ g.eval (Finset.univ.sup fun i => vecSize (r i)) ∧
        (∀ x ∈ cone (Set.range fun i => toReal (r i)), euclidNorm x = 1 →
          1 / (Finset.univ.sup' ⟨⟨0, hs⟩, Finset.mem_univ _⟩
                fun i => euclidNorm (toReal (r i))) ≤ ∑ j, (f j : ℝ) * x j) ∧
        Bornology.IsBounded (cone (Set.range fun i => toReal (r i)) ∩ hyperplane f) := by sorry

end MIQPInNP.SmallSol

