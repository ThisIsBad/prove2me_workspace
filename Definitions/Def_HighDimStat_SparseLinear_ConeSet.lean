import Mathlib

namespace HighDimStat.SparseLinear

/-- The cone `C_α(S) := {Δ ∈ ℝ^d | ‖Δ_{Sᶜ}‖₁ ≤ α‖Δ_S‖₁}` of Wainwright, *High-Dimensional
Statistics* (2019), Eq. (7.21), for a subset `S ⊆ {1,...,d}` and a constant `α ≥ 1`. The special
case `α = 1` is the set `C(S)` used to define the restricted nullspace property (p. 201). -/
def ConeSet {d : ℕ} (S : Finset (Fin d)) (α : ℝ) (Δ : Fin d → ℝ) : Prop :=
  (∑ j ∈ Sᶜ, |Δ j|) ≤ α * ∑ j ∈ S, |Δ j|

end HighDimStat.SparseLinear
