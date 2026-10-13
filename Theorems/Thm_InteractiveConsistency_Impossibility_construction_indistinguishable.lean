import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario
import Definitions.Def_InteractiveConsistency_Impossibility_Construction

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, proof of the THEOREM, p. 233: for a partition
`A, B, C` of `P` and any values `v, v'`, the scenarios of p. 232 satisfy `α(aw) = σ(aw)` and
`β(bw) = σ(bw)` for all `a ∈ A`, `b ∈ B` and strings `w`; that is, `α_a = σ_a` and `β_b = σ_b`
as `a`- and `b`-scenarios. -/
theorem construction_indistinguishable {α V : Type*} [DecidableEq α] (P A B C : Finset α)
    (v v' : V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hP : A ∪ B ∪ C = P) :
    (∀ a ∈ A, restrict (alphaScen P A B C v v') a = restrict (sigmaScen P A B C v v') a) ∧
    (∀ b ∈ B, restrict (betaScen P A B C v v') b = restrict (sigmaScen P A B C v v') b) := by sorry

end InteractiveConsistency.Impossibility

