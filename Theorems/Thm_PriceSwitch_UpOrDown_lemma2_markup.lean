import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

/-- Feng–Gallego (1995), Lemma 2, case (ii), p. 1379. The printed word "bounded" is corrected to
bounded away from zero: the thresholds tend to infinity. -/
theorem lemma2_markup (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkupPair a la b lb) :
    let y : ℕ → ℝ := fun n => sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0}
    (∀ n, 1 ≤ n → ∃ s, 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0) ∧
    0 < y 1 ∧
    StrictMonoOn y (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → ∀ s, 0 ≤ s → s < y n → 0 < PriceSwitch.Markdown.G a la b lb n s) ∧
    (∀ n, 1 ≤ n → ∀ s, y n < s → PriceSwitch.Markdown.G a la b lb n s < 0) := by sorry

end PriceSwitch.UpOrDown

