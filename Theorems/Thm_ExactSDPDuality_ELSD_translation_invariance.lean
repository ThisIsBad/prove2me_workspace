import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Translation invariance (Ramana 1997, §2.5, p. 150): for `x̄ ∈ G`, the sets `𝒞ₖ`, `𝒰ₖ` and
`𝒲ₖ` built from the data `(Q(x̄), Q₁, …, Qₘ)` coincide with those built from
`(Q₀, Q₁, …, Qₘ)`, for every `k`. -/
theorem translation_invariance {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (xbar : Fin m → ℝ) (hx : xbar ∈ feasibleSet Q0 Q) (k : ℕ) :
    (∀ U W : ℕ → Matrix (Fin n) (Fin n) ℝ,
        IsCSeq (Qaff Q0 Q xbar) Q k U W ↔ IsCSeq Q0 Q k U W) ∧
      Uset (Qaff Q0 Q xbar) Q k = Uset Q0 Q k ∧
      Wset (Qaff Q0 Q xbar) Q k = Wset Q0 Q k := by sorry

end ExactSDPDuality.ELSD
