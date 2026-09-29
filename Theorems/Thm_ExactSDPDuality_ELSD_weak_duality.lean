import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Theorem 6(i), weak duality, in the form proved on pp. 140–141 (Ramana 1997): if `x` is
primal feasible, `k ≤ m`, and `(U, W)` satisfies `Q*(U + W) = c`, `W ∈ 𝒲ₖ`, `U ⪰ 0`, then
`cᵀx ≤ (U + W) • Q₀`. With `k = m` this is weak duality for (ELSD), with `k = m − 1` for
(Weak-ELSD). -/
theorem weak_duality {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) (k : ℕ) (hk : k ≤ m)
    (x : Fin m → ℝ) (hx : x ∈ feasibleSet Q0 Q)
    (U W : Matrix (Fin n) (Fin n) ℝ) (hc : Qstar Q (U + W) = c)
    (hW : W ∈ Wset Q0 Q k) (hU : U.PosSemidef) :
    c ⬝ᵥ x ≤ frob (U + W) Q0 := by sorry

end ExactSDPDuality.ELSD
