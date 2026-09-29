import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_phiDiv
open Matrix

namespace PhiDivRobust.Counterpart

/-- The φ-divergence uncertainty region (Ben-Tal et al. 2013, p. 347, Eq. (12)):
`U = {p ∈ ℝᵐ | p ≥ 0, Cp ≤ d, I_φ(p, q) ≤ ρ}`, with `C ∈ ℝ^{k×m}`, `d ∈ ℝᵏ`. -/
def uncertaintySet {m k : ℕ} (φ : ℝ → EReal) (C : Matrix (Fin k) (Fin m) ℝ) (d : Fin k → ℝ)
    (q : Fin m → ℝ) (ρ : ℝ) : Set (Fin m → ℝ) :=
  {p | 0 ≤ p ∧ C *ᵥ p ≤ d ∧ phiDiv φ p q ≤ (ρ : EReal)}

/-- The probability-vector uncertainty region of Corollary 1 (Ben-Tal et al. 2013, p. 347):
`U = {p ∈ ℝᵐ | p ≥ 0, eᵀp = 1, I_φ(p, q) ≤ ρ}`. -/
def probUncertaintySet {m : ℕ} (φ : ℝ → EReal) (q : Fin m → ℝ) (ρ : ℝ) : Set (Fin m → ℝ) :=
  {p | 0 ≤ p ∧ ∑ i, p i = 1 ∧ phiDiv φ p q ≤ (ρ : EReal)}

end PhiDivRobust.Counterpart
