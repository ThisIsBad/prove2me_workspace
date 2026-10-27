import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P38

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-- PDF pp.8–9: CONDITIONAL reversal of common-randomness extraction. Question 4 is
an antecedent, never an available theorem. The two local randomizations are independent
given a single uniform shared seed, and no public discussion is allowed. -/
theorem commonRandomness_reversal (hquestion : QuestionFour)
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (error slack : ℝ) (he : 0 < error) (hs : 0 < slack) :
    ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
      ∃ seeds : ℕ, 0 < seeds ∧ Real.logb 2 (seeds : ℝ) / n ≤ sourceInformationBits p w + slack ∧
        ∃ (a : Fin seeds → SourceWord A n → ℝ) (b : Fin seeds → SourceWord B n → ℝ),
          IsStochastic a ∧ IsStochastic b ∧
          tv (jointWordLaw p w) (generatedPairs a b) ≤ error := by sorry

end QAlgorithms.Papers.Independent.Support50.P38

end

