import Mathlib

namespace OnlineStochMatching.SuggestedMatching

/-- The number of bins in `B` hit by `n` independent placements into `Fin n`. -/
noncomputable def occupiedIn (n : ℕ) (B : Finset (Fin n)) (ω : Fin n → Fin n) : ℕ := by
  classical
  exact (B.filter fun b => ∃ t, ω t = b).card

/-- Uniform counting probability on a finite sample space. -/
noncomputable def uniformProbability {Ω : Type} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

/-- Uniform counting expectation of a real-valued statistic. -/
noncomputable def uniformExpectation {Ω : Type} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω, X ω) / (Fintype.card Ω : ℝ)

end OnlineStochMatching.SuggestedMatching
