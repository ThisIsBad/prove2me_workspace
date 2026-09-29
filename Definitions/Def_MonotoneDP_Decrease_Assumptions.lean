import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model

namespace MonotoneDP.Decrease

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- Assumption D (uniform decrease), eq. (23): `J̄(x) ≥ H(x, u, J̄)` for all `x ∈ S`, `u ∈ U(x)`. -/
def AssumptionD : Prop := ∀ x, ∀ u ∈ m.U x, m.H x u m.Jbar ≤ m.Jbar x

/-- Assumption D.1, eq. (34): if `{J_k} ⊂ F` satisfies `J_{k+1} ≤ J_k ≤ J̄` for all `k`, then
`lim_k H(x, u, J_k) = H(x, u, lim_k J_k)` for all `x ∈ S`, `u ∈ U(x)`, where `lim_k J_k` is the
pointwise limit (it exists because the sequence is nonincreasing, and so does the left-hand
limit, by monotonicity of `H`). -/
def AssumptionD1 : Prop :=
  ∀ Js : ℕ → S → EReal, (∀ k, Js k ≤ m.Jbar) → (∀ k, Js (k + 1) ≤ Js k) →
    ∀ x, ∀ u ∈ m.U x,
      limUnder atTop (fun k => m.H x u (Js k)) =
        m.H x u (fun y => limUnder atTop (fun k => Js k y))

/-- Assumption D.2 with the scalar `α`, eq. (35): `α > 0` and for all scalars `r > 0` and all
`J ∈ F` with `J ≤ J̄`,
`H(x, u, J) − α r ≤ H(x, u, J − r e) ≤ H(x, u, J)` for all `x ∈ S`, `u ∈ U(x)`, where `e` is the unit
function. "D.2 holds" is `∃ α, m.AssumptionD2 α`. -/
def AssumptionD2 (α : ℝ) : Prop :=
  0 < α ∧ ∀ r : ℝ, 0 < r → ∀ J : S → EReal, J ≤ m.Jbar → ∀ x, ∀ u ∈ m.U x,
    m.H x u J - ((α * r : ℝ) : EReal) ≤ m.H x u (fun y => J y - (r : EReal)) ∧
      m.H x u (fun y => J y - (r : EReal)) ≤ m.H x u J

end Model

end MonotoneDP.Decrease
