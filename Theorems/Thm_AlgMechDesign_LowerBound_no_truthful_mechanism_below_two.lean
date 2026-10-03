import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

/-- Theorem 4.6 for truthful direct mechanisms (§4.3, p. 177): with at least two agents and at
least three tasks, no truthful direct mechanism for task scheduling has an allocation rule that
is a `c`-approximation for any `c < 2`. -/
theorem no_truthful_mechanism_below_two {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 3 ≤ k)
    {c : ℝ} (hc : c < 2) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay) :
    ¬ IsApprox c alloc := by sorry

end AlgMechDesign.LowerBound

