import Definitions.Def_ComputationalLearning_VC

open MeasureTheory


namespace ComputationalLearning

/-- **Lemma 3.1** (p. 55, Sauer's lemma). If `VCD(C) = d`, then for any `m`, `Π_C(m) ≤ Φ_d(m)`.
Stated for every class of VC dimension at most `d`. -/
theorem sauer_lemma {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (d : ℕ)
    (hd : vcDim C ≤ d) (m : ℕ) :
    growth C m ≤ Phi d m := by sorry

end ComputationalLearning

