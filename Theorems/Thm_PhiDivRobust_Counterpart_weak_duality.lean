import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix

namespace PhiDivRobust.Counterpart

/-- Ben-Tal et al. 2013, p. 347, proof of Theorem 1, duality step, the "if" direction (weak duality):
if `g(λ, η) ≤ β` for some `λ ≥ 0` and `η ≥ 0`, then `x` satisfies the robust constraint (11)
over the uncertainty region (12). -/
theorem weak_duality {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ)
    (h : ∃ lam : ℝ, ∃ η : Fin k → ℝ, 0 ≤ lam ∧ 0 ≤ η ∧
      dualFunction φ a B C d q ρ x lam η ≤ (β : EReal)) :
    ∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β := by sorry

end PhiDivRobust.Counterpart
