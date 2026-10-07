import Mathlib

namespace ConvexOptAlg.GoemansWilliamson

open Matrix

/-- The graph Laplacian (Bubeck, arXiv:1405.4980v2, §6.6, p. 344): `L = D − A`, where `D` is the
diagonal matrix with entries `(∑ⱼ A i j)_{i ∈ [n]}`. -/
noncomputable def laplacian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ∑ j, A i j) - A

/-- The Frobenius inner product `⟨M, X⟩ = Tr(M⊤X)` (Bubeck, §1.5, p. 240). -/
def frobInner {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace (Mᵀ * X)

/-- A vector of the hypercube `{−1, 1}ⁿ`: every coordinate is `1` or `−1`. -/
def IsSignVector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, x i = 1 ∨ x i = -1

/-- The encoding of a point of the hypercube by a Boolean vector: `true ↦ 1`, `false ↦ −1`.
It is a bijection from `Fin n → Bool` onto `{−1, 1}ⁿ`. -/
def signOfBool (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The value `max_{x ∈ {−1, 1}ⁿ} x⊤Mx` of the quadratic form of `M` over the hypercube
((6.7), p. 344, with `M = L`; (6.9), p. 346, with `M = B`). It is a maximum over the finite,
nonempty set of the `2ⁿ` Boolean vectors (each read as a `±1` vector by `signOfBool`). -/
def hypercubeMax {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun b : Fin n → Bool => (fun i => signOfBool (b i)) ⬝ᵥ M *ᵥ (fun i => signOfBool (b i)))

/-- A feasible point of the SDP relaxation (p. 345): `X ∈ S₊ⁿ` (symmetric positive
semidefinite) with `X i i = 1` for every `i ∈ [n]`. -/
def IsSDPFeasible {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.PosSemidef ∧ ∀ i, X i i = 1

/-- `Σ` is a solution of the SDP relaxation `max_{X ∈ S₊ⁿ, X i i = 1} ⟨M, X⟩` (p. 345 with
`M = L`; p. 346 with `M = B`): `Σ` is feasible and `⟨M, X⟩ ≤ ⟨M, Σ⟩` for every feasible `X`.
Any maximizer qualifies ("the solution" of the book need not be unique). -/
def IsSDPRelaxationOptimum {n : ℕ} (M Sig : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsSDPFeasible Sig ∧ ∀ X, IsSDPFeasible X → frobInner M X ≤ frobInner M Sig

/-- The sign function used for the rounding, with values in `{−1, 1}`: `sign(r) = 1` if `r ≥ 0`
and `−1` if `r < 0`. (Mathlib's `Real.sign` has `sign 0 = 0`; the book's `ζ = sign(ξ)` lies in
`{−1, 1}ⁿ`, so the value at `0` is fixed to `1`. The event `ξ i = 0` has probability `0` when
`Σ i i = 1`.) -/
noncomputable def sgn (r : ℝ) : ℝ :=
  if 0 ≤ r then 1 else -1

/-- The rounded vector `ζ = sign(ξ) ∈ {−1, 1}ⁿ`, coordinatewise. -/
noncomputable def sgnVec {n : ℕ} (ξ : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ :=
  fun i => sgn (ξ i)

end ConvexOptAlg.GoemansWilliamson
