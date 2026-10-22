import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

namespace LocalRademacher.Classif

/-- **Lemma 6.4** (Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, p. 29). For labels
`Yᵢ ∈ {±1}`, a class `F` of `{±1}`-valued classifiers and every `b ∈ [0, 1]` for which some
`f ∈ F` has `Pₙℓ_f ≤ b`,
`E_σ Rₙ{ℓ_f : f ∈ F, Pₙℓ_f ≤ b} = 1/2 − E_σ min{Pₙℓ(f(X), σ) : f ∈ F, Pₙℓ(f(X), Y) ≤ b}`,
both expectations being the average over the `2ⁿ` sign vectors. The feasibility hypothesis
`hfeas` is added: the page's `min` presupposes a nonempty feasible set. -/
theorem lemma_6_4 {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ b) :
    UnderstandingML.rademacher (lossVecs F xs ys b) =
      1 / 2 - (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ⨅ f : {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ b},
          empLoss xs (UnderstandingML.signVec σ) f.1 := by sorry

end LocalRademacher.Classif

