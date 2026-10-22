import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
open Finset

namespace LeviBalancing.DualBalancing

/-- Lemma 4.3, p. 294 (pathwise): for every demand realization and any two order processes with
nonnegative orders, the marginal backlogging cost of `B` over the periods
`𝒯_Π = {t : Y_t^B ≥ Y_t^P}` is at most the total marginal backlogging cost
`Π^P = ∑_{t=1}^{T−L} Π_t^P` of `P`. -/
theorem backlog_on_TPi_le (I : Instance) (d : ℤ → ℝ)
    (hd : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ d t) (qB qP : ℤ → ℝ)
    (hqB : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qB t)
    (hqP : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qP t) :
    ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qP t ≤ invPositionAfter I d qB t),
        marginalBacklog I d qB t ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), marginalBacklog I d qP t := by sorry

end LeviBalancing.DualBalancing

