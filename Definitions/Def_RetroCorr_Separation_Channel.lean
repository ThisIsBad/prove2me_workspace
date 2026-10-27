import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel

namespace RetroCorr.Separation

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Matrix

/-- Fig. 1, p. 2: the classical control output ("flag") of `R_{c,d}`: the random basis `B` of
`H_c`, represented by a unitary `W` whose columns `w_j = W e_j` are the basis vectors, together
with the `c` random unitaries `U_1, …, U_c` on `H_d`. -/
abbrev Flag (c d : ℕ) : Type :=
  Matrix.unitaryGroup (Fin c) ℂ × (Fin c → Matrix.unitaryGroup (Fin d) ℂ)

/-- Fig. 1, p. 2 ("random basis", "random unitaries"): the law of the flag. `B` (through `W`)
and `U_1, …, U_c` are independent and each is Haar distributed (the normalized Haar probability
measure `QAlgorithms.Schur.unitaryHaar` on the unitary group). -/
def flagLaw (c d : ℕ) : Measure (Flag c d) :=
  (QAlgorithms.Schur.unitaryHaar c).prod
    (Measure.pi fun _ : Fin c => QAlgorithms.Schur.unitaryHaar d)

/-- The projector `|w_j⟩⟨w_j|` onto the `j`-th vector of the basis `B` given by the columns of
`W`. -/
def basisProj {c : ℕ} (W : Matrix.unitaryGroup (Fin c) ℂ) (j : Fin c) :
    Matrix (Fin c) (Fin c) ℂ :=
  Matrix.of fun a b => (W : Matrix (Fin c) (Fin c) ℂ) a j * star ((W : Matrix (Fin c) (Fin c) ℂ) b j)

/-- §3, p. 3: the `j`-th projector of the basis `B^T`, the transpose `(|w_j⟩⟨w_j|)^T`
(`= |w̄_j⟩⟨w̄_j|`, the projector onto the complex-conjugate vector). -/
def transposeBasisProj {c : ℕ} (W : Matrix.unitaryGroup (Fin c) ℂ) (j : Fin c) :
    Matrix (Fin c) (Fin c) ℂ :=
  (basisProj W j)ᵀ

/-- Fig. 1, p. 2: the action of `R_{c,d}` for one value `k = (W, U_1, …, U_c)` of its classical
control output. The input is indexed by `(control, data)`. The channel measures the control in
the basis `B = {w_j}`, applies `U_j` to the data and forgets `j`:
`X ↦ Σ_j U_j Tr_c[(|w_j⟩⟨w_j| ⊗ I) X] U_j†`. -/
def retroBranch (c d : ℕ) (k : Flag c d) :
    QAlgorithms.Superop (Fin c × Fin d) (Fin d) :=
  fun X => ∑ j : Fin c,
    (k.2 j : Matrix (Fin d) (Fin d) ℂ) *
      QAlgorithms.traceLeft (Matrix.kronecker (basisProj k.1 j) (1 : Matrix (Fin d) (Fin d) ℂ) * X) *
      (k.2 j : Matrix (Fin d) (Fin d) ℂ)ᴴ

/-- §3, p. 3: the density matrix of the maximally entangled state
`Φ_c = c^{-1/2} Σ_a |a⟩|a⟩` on `(reference, control)`; for `c = 2` this is an ebit. -/
def maxEntDensity (c : ℕ) : Matrix (Fin c × Fin c) (Fin c × Fin c) ℂ :=
  Matrix.of fun p q => if p.1 = p.2 ∧ q.1 = q.2 then ((c : ℂ))⁻¹ else 0

end

end RetroCorr.Separation
