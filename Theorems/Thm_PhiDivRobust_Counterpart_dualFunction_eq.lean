import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_scaledConj
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix

namespace PhiDivRobust.Counterpart

/-- Ben-Tal et al. 2013, p. 347, Eq. (15): for `q > 0`, `λ ≥ 0` and `η ∈ ℝᵏ`, the dual objective
function separates over scenarios,
`g(λ, η) = aᵀx + dᵀη + ρλ + ∑ᵢ qᵢ (λφ)*(bᵢᵀx − cᵢᵀη)`, where `bᵢ`, `cᵢ` are the `i`-th columns of
`B` and `C`. -/
theorem dualFunction_eq {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (x : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (η : Fin k → ℝ) :
    dualFunction φ a B C d q ρ x lam η =
      ((a ⬝ᵥ x + d ⬝ᵥ η + ρ * lam : ℝ) : EReal) +
        ∑ i, (q i : EReal) *
          scaledConj φ lam ((fun j => B j i) ⬝ᵥ x - (fun j => C j i) ⬝ᵥ η) := by sorry

end PhiDivRobust.Counterpart
