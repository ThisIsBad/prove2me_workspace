import Mathlib
import Definitions.Def_Disjunctive_Dominants_Basic

namespace Disjunctive.Dominants

/-- Theorem 13.7 (Balas §13.2, p. 219-220), the goal theorem of this mission: `P⁺ = {x≥0 :
πx≥1 for every S⊆N and π∈I^S}`, and every such inequality is facet-defining for `P⁺`. `P` is nonempty: for `P = ∅` the only `π ∈ I^S` is `π = 0` at `S = ∅`, and the claimed facet
is the empty set. -/
theorem general_dominant_facet_characterization {n : ℕ} (P : Set (Fin n → ℝ))
    (hP : P.Nonempty) :
    Dominant P = {x | 0 ≤ x ∧ ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        1 ≤ dotProduct pi x} ∧
      ∀ (S : Finset (Fin n)) (pi : Fin n → ℝ), IsInIS S P pi →
        IsFacet (Dominant P) ({x ∈ Dominant P | dotProduct pi x = 1}) := by sorry

end Disjunctive.Dominants

