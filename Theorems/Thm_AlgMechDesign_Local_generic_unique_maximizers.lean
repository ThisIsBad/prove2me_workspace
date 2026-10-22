import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices

namespace AlgMechDesign.Local

/-- Lemma 4.13, p. 180: for a truthful mechanism, every positive type vector `t` and every
`ε > 0` there is a positive type vector `t'` with `‖t − t'‖ < ε` (sup norm) at which, for every
agent `i`, `xⁱ(t')` is the unique maximizer of `i`'s utility among the attainable sets. -/
theorem generic_unique_maximizers {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : Fin n → Fin k → ℝ, IsType t' ∧ ‖t - t'‖ < ε ∧
      ∀ i : Fin n, IsUniqueMaximizer alloc pay t' i := by sorry

end AlgMechDesign.Local

