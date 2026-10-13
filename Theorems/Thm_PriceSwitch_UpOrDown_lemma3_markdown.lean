import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

open Filter Topology

/-- Feng–Gallego (1995), Lemma 3, case (i), p. 1382, for `Δ(n, t) = J(n, t; t) − J(n, t; 0)` and
`t_n = inf{t > 0 : Δ(n, t) = 0}`. -/
theorem lemma3_markdown (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkdownPair a la b lb) :
    let Δ : ℕ → ℝ → ℝ := fun n t => PriceSwitch.Markdown.switchRevenue a la b lb n t t - PriceSwitch.Markdown.switchRevenue a la b lb n t 0
    let tn : ℕ → ℝ := fun n => sInf {t : ℝ | 0 < t ∧ Δ n t = 0}
    (∀ n, 1 ≤ n → Continuous (Δ n)) ∧
    (∀ n, 1 ≤ n → ∃ t, 0 < t ∧ Δ n t = 0) ∧
    (∀ n, 1 ≤ n → ∀ t, 0 < t → t < tn n → Δ n t < 0) ∧
    (∀ n, 1 ≤ n → ∀ t, tn n < t → 0 < Δ n t) ∧
    StrictMonoOn tn (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → MonotoneOn (Δ n) (Set.Ioi (tn n))) ∧
    (∀ n, 1 ≤ n → Tendsto (Δ n) atTop (𝓝 ((a - b) * n))) := by sorry

end PriceSwitch.UpOrDown

