import Mathlib

/-!
# The Cournot instance (7) and its closed forms (Sec. 3.2, p. 12; Sec. 4.1.2, pp. 19–20)

Cachon–Lariviere, *Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and
Limitations*, working paper (June 2000).
-/

namespace RevShareCoord.Competing

open Finset

/-- The Cournot revenue functions (7) (Sec. 3.2, p. 12):
`Rᵢ(q̄) = qᵢ (1 − qᵢ − β Σ_{j≠i} qⱼ)`, with `0 ≤ β < 1` in the paper. -/
def cournotRevenue {n : ℕ} (β : ℝ) (i : Fin n) (q : Fin n → ℝ) : ℝ :=
  q i * (1 - q i - β * ∑ j ∈ univ.erase i, q j)

/-- The symmetric equilibrium quantity `q_i^N = (1 − w)/(2 + β(n − 1))` at the common wholesale
price `w` (Sec. 4.1.2, p. 19). -/
noncomputable def cournotQN (β : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  (1 - w) / (2 + β * ((n : ℝ) - 1))

/-- The symmetric integrated-channel quantity `q_i^I = (1 − c)/(2 + 2β(n − 1))`
(Sec. 4.1.2, p. 19). -/
noncomputable def cournotQI (β : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  (1 - c) / (2 + 2 * β * ((n : ℝ) - 1))

/-- The coordinating wholesale price `w^I = c + β(n − 1)(1 − c)/(2 + 2β(n − 1))`
(Sec. 4.1.2, p. 19). -/
noncomputable def cournotWI (β : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  c + β * ((n : ℝ) - 1) * (1 - c) / (2 + 2 * β * ((n : ℝ) - 1))

end RevShareCoord.Competing
