import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_phiDiv
open Matrix

namespace PhiDivRobust.Counterpart

/-- The Lagrange function of the worst-case problem (14) (Ben-Tal et al. 2013, p. 347, proof of
Theorem 1): `L(p, λ, η) = (a + Bp)ᵀx + ρλ − λ ∑ᵢ qᵢ φ(pᵢ/qᵢ) + ηᵀ(d − Cp)`, valued in `EReal`. -/
noncomputable def lagrangian {n m k : ℕ} (φ : ℝ → EReal) (a : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ)
    (q : Fin m → ℝ) (ρ : ℝ) (x : Fin n → ℝ) (p : Fin m → ℝ) (lam : ℝ) (η : Fin k → ℝ) : EReal :=
  (((a + B *ᵥ p) ⬝ᵥ x + ρ * lam + η ⬝ᵥ (d - C *ᵥ p) : ℝ) : EReal) - (lam : EReal) * phiDiv φ p q

/-- The dual objective function `g(λ, η) = max_{p ≥ 0} L(p, λ, η)` (Ben-Tal et al. 2013, p. 347,
proof of Theorem 1). The paper's `max` is read as a supremum in `EReal` (it need not be attained and
may be `+∞`). -/
noncomputable def dualFunction {n m k : ℕ} (φ : ℝ → EReal) (a : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ)
    (q : Fin m → ℝ) (ρ : ℝ) (x : Fin n → ℝ) (lam : ℝ) (η : Fin k → ℝ) : EReal :=
  ⨆ p ∈ {p : Fin m → ℝ | 0 ≤ p}, lagrangian φ a B C d q ρ x p lam η

end PhiDivRobust.Counterpart
