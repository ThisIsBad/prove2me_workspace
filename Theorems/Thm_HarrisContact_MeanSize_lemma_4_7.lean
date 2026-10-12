import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Lemma 4.7, p. 975: for a contact process started from a finite
set `ξ`, `m_t(ξ) ≤ |ξ| e^{(2dΛ − μ)t}` for `t ≥ 0`, where `Λ = max_{0 ≤ i ≤ 2d} λ_i`. -/
theorem lemma_4_7 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (t : ℝ) (ht : 0 ≤ t) (ξ : HarrisContact.Extinction.Config d) :
    HarrisContact.Extinction.meanSize μ lam t ξ ≤ (ξ.card : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp ((2 * (d : ℝ) * (Finset.range (2 * d + 1)).sup' (by simp) lam - μ) * t)) := by sorry
end HarrisContact.MeanSize

