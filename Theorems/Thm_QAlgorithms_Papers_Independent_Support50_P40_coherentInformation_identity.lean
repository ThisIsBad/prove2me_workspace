import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.14--15, Eqs.(21)--(30): both diagonalizations, both entropy
identities, and coherent information per use for this same code and input.
Eq.(29)'s printed `1/2` amplitudes are corrected as explained in `codeBellInput`.
Neither an input maximization nor a general capacity formula is asserted. -/
theorem coherentInformation_identity {m : ℕ} (C : InnerCode m) (T : CosetChoices C)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    IsState (codeBellInput C) ∧ IsDensityMatrix (outputQ C f) ∧ IsDensityMatrix (outputRQ C f) ∧
    Orthonormal ℂ (fun ib : Qubits m × Bool => errorBasis C T ib.1 ib.2) ∧
    Orthonormal ℂ (fun ij : Qubits m × Pauli => bellBasis C T ij.1 ij.2) ∧
    outputQ C f = ∑ ib : Qubits m × Bool,
      ((syndromeMass C T f ib.1 / 2 : ℝ) : ℂ) • pureDensity (errorBasis C T ib.1 ib.2) ∧
    outputRQ C f = ∑ ij : Qubits m × Pauli,
      (jointMass C T f ij.1 ij.2 : ℂ) • pureDensity (bellBasis C T ij.1 ij.2) ∧
    vnEntropy (outputQ C f) = 1 + finiteEntropyBits (syndromeMass C T f) ∧
    vnEntropy (outputRQ C f) = finiteEntropyBits (fun ij : Qubits m × Pauli => jointMass C T f ij.1 ij.2) ∧
    (vnEntropy (outputQ C f) - vnEntropy (outputRQ C f)) / (m + 1) = signedYield C T f := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40

