import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from pinned accepted modules, under the independent-paper override.
-- No coding theorem or other paper's channel model is reused.

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}

variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]

variable [Fintype A] [Fintype B]

variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]

variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

/-- Appendix B, Lemma 3, PDF pp.16–19, equations (139)–(140).
Printed: p.17 frequency sets omit support and the marginal sentence keeps the same tolerance;
p.19 (174) equates a product with its linear lower bound.
Changed: exclude impossible input/eigenword symbols, choose eta and N after both positive
projector tolerances and before all words, and read (174) as a lower bound.
Why: impossible inputs can give zero projector acceptance, marginalization sums frequency
errors (as (152)–(154) explicitly account for), and the product has positive cross terms.
Both original acceptance conclusions and the block projectors (170) are retained.
Independently audited in MODERATION-r1.md; items.json records printed/changed/why. -/
theorem typical_projectors_accept (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Sbar : FiniteSpectralResolution B1 (averageState1 C D))
    (Scond : ∀ u, FiniteSpectralResolution B1 (conditionalState1 C D u)) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ deltaBar : ℝ, 0 < deltaBar → ∀ deltaCond : ℝ, 0 < deltaCond →
    ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      ∀ (u : Fin n → U) (v : Fin n → V),
        StrongTypical D.law.prob eta (fun i => (u i, v i)) →
        1 - epsilon ≤ effectProb (averagedProjector Sbar n deltaBar) (receiver1Word C D u v) ∧
        1 - epsilon ≤ effectProb (conditionalTypicalProjector C D Scond u deltaCond)
          (receiver1Word C D u v) := by sorry

end QAlgorithms.Papers.Independent.Support50.P26

end

