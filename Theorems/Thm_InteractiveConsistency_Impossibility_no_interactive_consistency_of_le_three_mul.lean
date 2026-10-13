import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, THEOREM, p. 232 (with the printed hypothesis
`n ≥ 3m` corrected to `n ≤ 3m`, as the proof and the section title require, and with the implicit
`n ≥ 3` of the proof made explicit): if `|V| ≥ 2` and `3 ≤ n ≤ 3m`, where `n = |P|`, there exists no
family `{F_p | p ∈ P}` that assures interactive consistency for `m` faults. -/
theorem no_interactive_consistency_of_le_three_mul {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hV : ∃ v v' : V, v ≠ v')
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∀ F : α → (List α → V) → α → V, ¬ AssuresIC P m F := by sorry

end InteractiveConsistency.Impossibility

