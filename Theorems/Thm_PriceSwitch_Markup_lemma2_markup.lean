import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markup

/-- Feng–Gallego (1995), Lemma 2, case (ii), p. 1379. The printed word "bounded" is replaced
by bounded away from zero, as required by the surrounding text and the actual sign pattern. -/
theorem lemma2_markup (a la b lb : ℝ) (hpair : PriceSwitch.Markdown.IsMarkupPair a la b lb) :
    (∀ n : ℕ, 1 ≤ n → ∃ s : ℝ, 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0) ∧
    0 < sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb 1 s = 0} ∧
    StrictMonoOn (fun n : ℕ => sInf {s : ℝ | 0 ≤ s ∧ PriceSwitch.Markdown.G a la b lb n s = 0})
      (Set.Ici 1) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, 0 ≤ s →
      s < sInf {u : ℝ | 0 ≤ u ∧ PriceSwitch.Markdown.G a la b lb n u = 0} → 0 < PriceSwitch.Markdown.G a la b lb n s) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ s : ℝ,
      sInf {u : ℝ | 0 ≤ u ∧ PriceSwitch.Markdown.G a la b lb n u = 0} < s → PriceSwitch.Markdown.G a la b lb n s < 0) := by sorry

end PriceSwitch.Markup

