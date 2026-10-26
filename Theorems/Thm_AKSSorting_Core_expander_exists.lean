import Mathlib
import Definitions.Def_AKSSorting_Core_IsExpander

namespace AKSSorting.Core

/-- Lemma 3 (Ajtai–Komlós–Szemerédi 1983, p. 6): for all `0 < ε < 1` and `c ≥ 1` there is a
positive integer `k = k(ε, c)` such that for all disjoint finite sets `A, B` with
`1/c ≤ |A|/|B| ≤ c` there is a `⟨k, ε⟩` expander on `⟨A, B⟩`. The ratio condition is written
multiplicatively, `|A| ≤ c|B|` and `|B| ≤ c|A|`. -/
theorem expander_exists (ε c : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hc : 1 ≤ c) :
    ∃ k : ℕ, 0 < k ∧ ∀ (V : Type) (A B : Finset V), Disjoint A B →
      (A.card : ℝ) ≤ c * B.card → (B.card : ℝ) ≤ c * A.card →
      ∃ G : SimpleGraph V, IsExpander G A B k ε := by sorry

end AKSSorting.Core

