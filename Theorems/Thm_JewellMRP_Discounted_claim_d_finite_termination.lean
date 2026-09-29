import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Claim (d), p. 946: every run of the algorithm of Fig. 1 produces two identical successive
policies within at most as many cycles as there are stationary policies. -/
theorem claim_d_finite_termination {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty A] (M : MRP S A) {α : ℝ} (hα : 0 < α) {d : ℕ → S → A} {v : ℕ → S → ℝ}
    (hrun : IsFig1Run M α d v) :
    ∃ K, K < Fintype.card (S → A) ∧ d (K + 1) = d K := by sorry

end JewellMRP.Discounted
