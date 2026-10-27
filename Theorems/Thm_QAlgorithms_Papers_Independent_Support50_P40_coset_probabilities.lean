import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.7--8,13, five probability interpretations and Eqs.(18)--(19).
All logical actions are compared on the entire encoded operator algebra;
the recovered branch retains its mass even for zero-probability syndromes. -/
theorem coset_probabilities {m : ℕ} (C : InnerCode m) (T : CosetChoices C)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    weightPolynomial f (stabilizerLabels C.stabilizer) =
      errorEventMass f (fun e : ErrorLabel (m + 1) =>
        ∀ rho : Matrix Bool Bool ℂ,
          conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) rho) =
            conjSuperop (innerEncoderMatrix C) rho) ∧
    (∀ j : Pauli, j ≠ .I →
      weightPolynomial f (labelCoset (T.logicalRep j) (stabilizerLabels C.stabilizer)) =
        errorEventMass f (fun e : ErrorLabel (m + 1) =>
          e ∈ centralizerLabels C.stabilizer ∧ ∀ rho : Matrix Bool Bool ℂ,
            conjSuperop (pauliOps e) (conjSuperop (innerEncoderMatrix C) rho) =
              conjSuperop (innerEncoderMatrix C) (conjSuperop j.mat rho))) ∧
    weightPolynomial f (centralizerLabels C.stabilizer) =
      effectProb (syndromeProjector C T (fun _ => false)) (outputQ C f) ∧
    (∀ i, syndromeMass C T f i =
      effectProb (syndromeProjector C T i) (outputQ C f)) ∧
    (∀ i j, jointMass C T f i j =
      effectProb (pureDensity (bellBasis C T i j)) (outputRQ C f)) ∧
    (∀ i (rho : Matrix Bool Bool ℂ), recoveredBranch C T f i rho =
      ∑ j : Pauli, (jointMass C T f i j : ℂ) • conjSuperop j.mat rho) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40

