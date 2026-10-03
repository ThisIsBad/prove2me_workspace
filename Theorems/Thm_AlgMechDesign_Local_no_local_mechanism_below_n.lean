import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices

namespace AlgMechDesign.Local

/-- Theorem 4.12, p. 180: there does not exist a local truthful mechanism for task scheduling
that is a `c`-approximation for any `c < n` (with `k ≥ n²` tasks, as in the proof). -/
theorem no_local_mechanism_below_n (n k : ℕ) [NeZero n] (hk : n ^ 2 ≤ k) (c : ℝ)
    (hc : c < n) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hloc : IsLocal alloc pay) : ¬ IsApprox c alloc := by sorry

end AlgMechDesign.Local

