import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario
import Definitions.Def_InteractiveConsistency_Impossibility_Construction

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, proof of the THEOREM, p. 233: for a partition
`A, B, C` of `P` and any values `v, v'`, the scenarios `α`, `β`, `σ` defined by (i)–(iii) of p. 232
are consistent with `N = A ∪ C`, `B ∪ C`, `A ∪ B`, respectively. -/
theorem construction_consistent {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hP : A ∪ B ∪ C = P) :
    ConsistentWith P (A ∪ C) (alphaScen P A B C v v') ∧
    ConsistentWith P (B ∪ C) (betaScen P A B C v v') ∧
    ConsistentWith P (A ∪ B) (sigmaScen P A B C v v') := by sorry

end InteractiveConsistency.Impossibility

