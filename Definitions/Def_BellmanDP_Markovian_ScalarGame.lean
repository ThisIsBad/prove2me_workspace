import Mathlib

namespace BellmanDP.Markovian

/-- Bellman, *Dynamic Programming*, Ch. XI, § 13, (13.1), p. 333: the bilinear form
`(Ap, q) = Σ_i q_i (Ap)_i` of an `m × n` matrix `A`, a vector `p ∈ ℝⁿ` and a vector `q ∈ ℝᵐ`. -/
def pairing {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ) : ℝ :=
  dotProduct q (A.mulVec p)

/-- Ch. XI, § 13, (13.2), p. 333: the right-hand side
`Max_p Min_q [(Ap, q) − (Bp, q) u]`, `p` and `q` ranging over probability vectors (the standard
simplices of `ℝⁿ` and `ℝᵐ`). Both simplices are compact and the payoff is continuous, so for
`m, n ≥ 1` the supremum and infimum are attained and are the book's `Max` and `Min`. -/
noncomputable def gameRHS {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (u : ℝ) : ℝ :=
  sSup ((fun p => sInf ((fun q => pairing A p q - pairing B p q * u) ''
    stdSimplex ℝ (Fin m))) '' stdSimplex ℝ (Fin n))

/-- Ch. XI, § 13, (13.3), p. 333: `Max_p Min_q (Ap, q)/(Bp, q)` over probability vectors. -/
noncomputable def maxMinRatio {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup ((fun p => sInf ((fun q => pairing A p q / pairing B p q) ''
    stdSimplex ℝ (Fin m))) '' stdSimplex ℝ (Fin n))

/-- Ch. XI, § 13, (13.3), p. 333: `Min_q Max_p (Ap, q)/(Bp, q)` over probability vectors. -/
noncomputable def minMaxRatio {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sInf ((fun q => sSup ((fun p => pairing A p q / pairing B p q) ''
    stdSimplex ℝ (Fin n))) '' stdSimplex ℝ (Fin m))

end BellmanDP.Markovian
