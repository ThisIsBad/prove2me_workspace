import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Lemma 9 (Ramana 1997, p. 140): for `k ≤ m`, `x ∈ G`, `U ∈ 𝒰ₖ` and `W ∈ 𝒲ₖ`,
`Q(x)U = 0` and `Q(x)W = 0`, hence `Q(x) • U = 0 = Q(x) • W`; in particular, if `0 ∈ G`
then `Q₀ • U = 0 = Q₀ • W`. -/
theorem lemma9 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) (k : ℕ) (hk : k ≤ m) :
    (∀ x ∈ feasibleSet Q0 Q, ∀ U ∈ Uset Q0 Q k, ∀ W ∈ Wset Q0 Q k,
        Qaff Q0 Q x * U = 0 ∧ Qaff Q0 Q x * W = 0 ∧
          frob (Qaff Q0 Q x) U = 0 ∧ frob (Qaff Q0 Q x) W = 0) ∧
      ((0 : Fin m → ℝ) ∈ feasibleSet Q0 Q →
        ∀ U ∈ Uset Q0 Q k, ∀ W ∈ Wset Q0 Q k, frob Q0 U = 0 ∧ frob Q0 W = 0) := by sorry

end ExactSDPDuality.ELSD
