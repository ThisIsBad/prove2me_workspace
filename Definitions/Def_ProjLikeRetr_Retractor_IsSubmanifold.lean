import Mathlib

namespace ProjLikeRetr.Retractor

/-- §2.1, p. 3: `M` is, around `x̄ ∈ M`, a `C^k` submanifold of dimension `d` of the Euclidean
space `E` (of dimension `n = finrank ℝ E`), in the sense of a coordinate slice: there are an open
neighbourhood `U` of `x̄` and a `C^k` diffeomorphism `φ` of `U` onto an open subset of `ℝⁿ` with
`M ∩ U = {x ∈ U | φ_{d+1}(x) = ⋯ = φ_n(x) = 0}`. Coordinates are 0-based, so the page's
`φ_{d+1}, …, φ_n` are the coordinates `i` with `d ≤ i`. -/
def IsSubmanifoldAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (xbar : E) : Prop :=
  d ≤ Module.finrank ℝ E ∧ xbar ∈ M ∧
    ∃ φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      xbar ∈ φ.source ∧ ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source ∧
      ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target ∧
      M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ x i = 0}

/-- §2.1, p. 3: `M` is a `C^k` submanifold of dimension `d` of `E`: a coordinate slice around
each of its points. -/
def IsSubmanifold {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) : Prop :=
  ∀ x ∈ M, IsSubmanifoldAt k d M x

end ProjLikeRetr.Retractor
