import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Lemma 4.11, p. 976: `m_{t+h}(ξ) ≥ e^{−μh} m_t(ξ)` for `t, h ≥ 0`
(drafted for finite `ξ`). -/
theorem lemma_4_11 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ t h : ℝ, 0 ≤ t → 0 ≤ h → ∀ ξ : HarrisContact.Extinction.Config d,
      ENNReal.ofReal (Real.exp (-(μ * h))) * HarrisContact.Extinction.meanSize μ lam t ξ ≤ HarrisContact.Extinction.meanSize μ lam (t + h) ξ := by sorry
end HarrisContact.MeanSize

