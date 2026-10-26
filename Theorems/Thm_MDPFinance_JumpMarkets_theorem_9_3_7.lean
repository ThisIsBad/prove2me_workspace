import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- Two jump markets with the same market data, differing only in the utility. -/
def JumpMarket.SameMarket {d : ℕ} (M M' : JumpMarket d) : Prop :=
  M'.rho = M.rho ∧ M'.mu = M.mu ∧ M'.lam = M.lam ∧ M'.QY = M.QY ∧ M'.T = M.T

/-- **Theorem 9.3.7** (p. 290), for the contracting model (`b = b_γ`, `α_b < 1`). a) If `U`,
`Ũ` are two utility functions (same market) with value functions `V`, `Ṽ`, then `‖V - Ṽ‖_b ≤
‖U - Ũ‖_b e^{T\barμ}/(1-α_b)` (in `≤`-form against `b`, two-sided in `[0,∞]`). b) If `(U^{(n)})`
are utility functions with `‖U^{(n)} - U‖_b → 0` and `V^{(n)}` their value functions, then
`∅ ≠ Ls A^*_n(t,x) ⊂ A^*(t,x)` on `E`, the maximum-point sets over the relaxed controls `R`
with the Young topology. -/
theorem theorem_9_3_7 {d : ℕ} (M Mtilde : JumpMarket d)
    (gamma alpha : ℝ) (hb : M.IsBoundingFunction (M.bfun gamma) alpha)
    (hbt : Mtilde.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1)
    (hsame : M.SameMarket Mtilde)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    (∀ C : ℝ, (∀ p ∈ M.E, |M.U p.2 - Mtilde.U p.2| ≤ C * M.bfun gamma p) →
      ∀ p ∈ M.E,
        M.V Pr p ≤ Mtilde.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p) ∧
          Mtilde.V Pr p ≤ M.V Pr p +
            ENNReal.ofReal (C * Real.exp (M.T * M.mubar) / (1 - alpha) * M.bfun gamma p)) ∧
    (∀ Mn : ℕ → JumpMarket d, (∀ n, M.SameMarket (Mn n)) →
      (∀ n, (Mn n).IsBoundingFunction (M.bfun gamma) alpha) →
      (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ p ∈ M.E,
        |(Mn n).U p.2 - M.U p.2| ≤ ε * M.bfun gamma p) →
      ∀ p ∈ M.E,
        (LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p)).Nonempty ∧
        LsSeq (fun n => (Mn n).AstarRel ((Mn n).V Pr) p) ⊆ M.AstarRel (M.V Pr) p) := by sorry

end MDPFinance.JumpMarkets

