import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model

namespace MonotoneDP.Increase

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- Assumption I (uniform increase), eq. (22): `J̄(x) ≤ H(x, u, J̄)` for all `x ∈ S`, `u ∈ U(x)`. -/
def AssumptionI : Prop := ∀ x, ∀ u ∈ m.U x, m.Jbar x ≤ m.H x u m.Jbar

/-- Assumption I.1, eq. (32): if `{J_k} ⊂ F` satisfies `J̄ ≤ J_k ≤ J_{k+1}` for all `k`, then
`lim_k H(x, u, J_k) = H(x, u, lim_k J_k)` for all `x ∈ S`, `u ∈ U(x)`, where `lim_k J_k` is the
pointwise limit (it exists because the sequence is nondecreasing). -/
def AssumptionI1 : Prop :=
  ∀ Js : ℕ → S → EReal, (∀ k, m.Jbar ≤ Js k) → (∀ k, Js k ≤ Js (k + 1)) →
    ∀ x, ∀ u ∈ m.U x,
      limUnder atTop (fun k => m.H x u (Js k)) =
        m.H x u (fun y => limUnder atTop (fun k => Js k y))

/-- Assumption I.2 with the scalar `α`, eq. (33): `α > 0` and for all scalars `r > 0` and all
`J ∈ F` with `J̄ ≤ J`,
`H(x, u, J) ≤ H(x, u, J + r e) ≤ H(x, u, J) + α r` for all `x ∈ S`, `u ∈ U(x)`, where `e` is the unit
function. "I.2 holds" is `∃ α, m.AssumptionI2 α`. -/
def AssumptionI2 (α : ℝ) : Prop :=
  0 < α ∧ ∀ r : ℝ, 0 < r → ∀ J : S → EReal, m.Jbar ≤ J → ∀ x, ∀ u ∈ m.U x,
    m.H x u J ≤ m.H x u (fun y => J y + (r : EReal)) ∧
      m.H x u (fun y => J y + (r : EReal)) ≤ m.H x u J + ((α * r : ℝ) : EReal)

end Model

end MonotoneDP.Increase
