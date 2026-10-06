import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, equilibrium condition under revenue sharing (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `φ ∈ [0, 1]` and let retailer `i` be offered the
revenue-sharing contract `(φ, wᵢ(φ))`. Every Nash equilibrium `q̄^N` of the retailers' game with
all entries positive satisfies `φ R_i^i(q̄^N) = wᵢ(φ)` for `i = 1, …, n`. -/
theorem revenue_sharing_equilibrium_foc {n : ℕ} (M : Model n) (φ : ℝ)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (w : Fin n → ℝ) (qN : Fin n → ℝ)
    (hN : IsNashEquilibrium M.R φ w qN) (hpos : ∀ i, 0 < qN i) :
    ∀ i, φ * M.dR i i qN = w i := by sorry

end RevShareCoord.Competing

