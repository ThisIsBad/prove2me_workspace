import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model
import Definitions.Def_AlgMechDesign_LowerBound_Mechanism

namespace AlgMechDesign.LowerBound

universe u

/-- Theorem 4.6: with at least two agents and at least three tasks, no mechanism — with
arbitrary strategy sets `A i`, output function `o` and payments `p` — implements a
`c`-approximation for the task scheduling problem with dominant strategies, for any `c < 2`. -/
theorem no_mechanism_below_two {n k : ℕ} [NeZero n] (hn : 2 ≤ n) (hk : 3 ≤ k) {c : ℝ}
    (hc : c < 2) {A : Fin n → Type u} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) :
    ¬ Implements o p c := by sorry

end AlgMechDesign.LowerBound

