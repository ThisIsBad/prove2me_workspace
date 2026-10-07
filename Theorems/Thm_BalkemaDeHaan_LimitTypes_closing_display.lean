import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Proof of Theorem 1, closing display, p. 797 (PDF 6): each limit law `G = 1 - S` of the four
families satisfies `min(1, S(B(t) + x A(t)) / S(t)) = S(x)` for every `t > 0`, with some
`A(t) > 0` and `B(t)`. -/
theorem closing_display :
    (∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiLaw (B + x * A)) / (1 - PiLaw t)) = 1 - PiLaw x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiDiscreteLaw γ (B + x * A)) / (1 - PiDiscreteLaw γ t)) =
        1 - PiDiscreteLaw γ x) ∧
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaLaw α (B + x * A)) / (1 - GammaLaw α t)) = 1 - GammaLaw α x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaDiscreteLaw γ α (B + x * A)) / (1 - GammaDiscreteLaw γ α t)) =
        1 - GammaDiscreteLaw γ α x) := by sorry

end BalkemaDeHaan.LimitTypes

