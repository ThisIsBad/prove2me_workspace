import Mathlib

namespace HighDimProb.RandomMatrices

/-- **Definition 4.2.14** (Hamming cube), Vershynin, *High-Dimensional Probability* (2018),
p. 85: the Hamming distance between two binary strings `x, y ∈ {0,1}ⁿ` is the number of bits
where they disagree. Binary strings of length `n` are represented as `Fin n → Bool`. -/
def hammingDist {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

end HighDimProb.RandomMatrices
