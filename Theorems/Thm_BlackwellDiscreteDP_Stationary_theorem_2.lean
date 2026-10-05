import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 2, p. 720 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"If (f, π) > π, then f^(∞) > π."

Both `>` are Blackwell's strict vector order (p. 720): `w₁ > w₂` iff `w₁ ≧ w₂` coordinatewise
and `w₁ ≠ w₂` (not coordinatewise strict). The discount factor is fixed, `0 ≤ β < 1`. -/
theorem theorem_2 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act) (π : Policy St Act)
    (h : M.V β π ≤ M.V β (Policy.cons f π) ∧ M.V β (Policy.cons f π) ≠ M.V β π) :
    M.V β π ≤ M.V β (stationary f) ∧ M.V β (stationary f) ≠ M.V β π := by sorry

end BlackwellDiscreteDP.Stationary

