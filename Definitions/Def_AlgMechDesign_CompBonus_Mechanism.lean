import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model

namespace AlgMechDesign.CompBonus

open Finset

/-- The compensation of agent `i` (Def. 21): `cⁱ(d, t̃) = ∑_{j ∈ xⁱ(d)} t̃_j`, where `x = alloc`
is the allocation algorithm, `d` the declarations and `t̃ = tt` the actual times. -/
def compensation {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => alloc d j = i), tt j

/-- The bonus of agent `i` (Def. 23): `bⁱ(d, t̃) = -g(x(d), corrⁱ(x(d), d, t̃))`, computed from
the declarations of the other agents and the actual times of agent `i`'s own tasks. -/
noncomputable def bonus {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  -gT (alloc d) (corr i (alloc d) d tt)

/-- The Compensation-and-Bonus payment based on the allocation algorithm `alloc` (Def. 24):
`pⁱ(d, t̃) = cⁱ(d, t̃) + bⁱ(d, t̃)`, the amount handed to agent `i`. The Compensation-and-Bonus
mechanism is the pair `(alloc, cbPay alloc)` with `alloc` an optimal allocation algorithm. -/
noncomputable def cbPay {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  compensation alloc d tt i + bonus alloc d tt i

end AlgMechDesign.CompBonus
