import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §4.3.4, Definition 4.3.4 (Partial Trace).

"Let `X_{AB}` be a square operator acting on a tensor product Hilbert space `ℋ_A ⊗ ℋ_B`, and let
`{|l⟩_B}` be an orthonormal basis for `ℋ_B`. Then the partial trace over the Hilbert space `ℋ_B`
is defined as `Tr_B{X_{AB}} ≡ ∑_l (I_A ⊗ ⟨l|_B) X_{AB} (I_A ⊗ |l⟩_B)`."

A bipartite operator is a matrix indexed by the product type `a × b` (the Kronecker convention
of Mathlib's `⊗ₖ`), and the orthonormal basis `{|l⟩_B}` is the standard basis of `b`.
-/

namespace WildeQIT

/-- **Definition 4.3.4 (Partial Trace over the right factor `B`).** For
`X : Matrix (a × b) (a × b) ℂ`, `Tr_B{X}` is the `a × a` matrix with entries
`(Tr_B X)ᵢⱼ = ∑ₖ X₍ᵢ,ₖ₎,₍ⱼ,ₖ₎`. -/
def partialTraceRight {a b : Type} [Fintype b] (X : Matrix (a × b) (a × b) ℂ) : Matrix a a ℂ :=
  Matrix.of fun i j => ∑ k, X (i, k) (j, k)

/-- **Definition 4.3.4 (Partial Trace over the left factor `A`).** For
`X : Matrix (a × b) (a × b) ℂ`, `Tr_A{X}` is the `b × b` matrix with entries
`(Tr_A X)ₖₗ = ∑ᵢ X₍ᵢ,ₖ₎,₍ᵢ,ₗ₎`. -/
def partialTraceLeft {a b : Type} [Fintype a] (X : Matrix (a × b) (a × b) ℂ) : Matrix b b ℂ :=
  Matrix.of fun k l => ∑ i, X (i, k) (i, l)

end WildeQIT
