import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory

namespace MDPFinance.LPDuality

/-- **Theorem 7.5.8 (Strong duality)** (Bäuerle–Rieder, p. 218, PDF 229, the goal theorem of this
mission). Suppose the assumptions of Theorem 7.3.5 (chunk `07a`'s goal, restated here as
hypotheses) are satisfied for the closed subspace `IM \subset IB_b`. Then the following
statements hold: a) `(P)` has an optimal solution `v^* \in IM`, `v^* = J_\infty` and `val(P) =
\int J_\infty(x)\,p(dx) = val(D)`. b) `(D)` has an optimal solution `\mu^* \in M_b` and there
exists an `f^* \in F` such that `val(D) = \int r\,d\mu^* = \int J_{f^*}(x)\,p(dx)`. In particular,
the stationary policy `(f^*,f^*,\dots)` is `p`-optimal. `IM` is a closed linear subspace of
`IB_b` (which gives `0 ∈ IM` and closedness, Theorem 7.3.5's (i)). -/
theorem theorem_7_5_8 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (hαb : M.β * αb < 1) (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (hTmaps : ∀ v ∈ IMs, (fun x => T' M v x) ∈ IMs) (Δ : Set (E → A))
    (hmax : ∀ v ∈ IMs, ∃ f ∈ Δ, IsMaximizerOf M (fun x => (v x : EReal)) f)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤) :
    (∃ vstar ∈ IMs, (∀ x, Jinf M x = (vstar x : EReal)) ∧ vstar ∈ ZP M IMs ∧
        ((∫ x, vstar x ∂p : ℝ) : EReal) = valP M IMs p ∧
        valP M IMs p = valD M b IMs p) ∧
      (∃ μstar ∈ ZD M b IMs p, ∃ fstar : E → A, IsMaximizerOf M (Jinf M) fstar ∧
        valD M b IMs p = ((∫ xa, M.r xa ∂μstar : ℝ) : EReal) ∧
        valD M b IMs p = erealIntegral p (fun x => Jinfpi M M.r (fun _ => fstar) x) ∧
        IsPOptimal M p (fun _ => fstar)) := by sorry

end MDPFinance.LPDuality
