import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Increase_Epigraph

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 457, Lemma 2: under Assumption I, for all `k ≥ 1`,
`P(C_k) ⊆ \overline{P(C_k)} = E[T^k(J̄)]` (eq. (58)); and
`P(C_k) = \overline{P(C_k)} = E[T^k(J̄)]` (eq. (59)) holds iff for each `x ∈ S` the infimum
`T^k(J̄)(x) = inf_{u ∈ U(x)} H[x, u, T^{k−1}(J̄)]` (eq. (60)) is attained. -/
theorem lemma2_projection_epigraph {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    ∀ k : ℕ, 1 ≤ k →
      (m.P (m.Ck k) ⊆ Pbar (m.P (m.Ck k)) ∧
        Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ∧
      ((m.P (m.Ck k) = Pbar (m.P (m.Ck k)) ∧
          Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ↔
        ∀ x : S, ∃ u ∈ m.U x,
          m.H x u ((m.T)^[k - 1] m.Jbar) =
            ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar)) := by sorry

end MonotoneDP.Increase
