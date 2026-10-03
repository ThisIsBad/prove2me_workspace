import Mathlib

namespace HunterPDE.Regularity

/-- Definition 4.51 of Hunter, *Notes on PDEs*: the `i`th difference quotient of `u : ℝⁿ → ℝ` of
size `h`, `D_i^h u(x) = (u(x + h eᵢ) − u(x)) / h`, where `eᵢ = EuclideanSpace.single i 1` is the
unit vector in the `i`th direction. Coordinates are 0-based (`i : Fin n` is the book's `i + 1`).
The book takes `h ∈ ℝ ∖ {0}`; at `h = 0` Lean's division gives the junk value `0`, and every
statement using `diffQuot` assumes `h ≠ 0`. -/
noncomputable def diffQuot {n : ℕ} (i : Fin n) (h : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (u (x + h • EuclideanSpace.single i (1 : ℝ)) - u x) / h

/-- The pointwise Euclidean length `|D^h u(x)| = (∑ᵢ (D_i^h u(x))²)^{1/2}` of the vector of
difference quotients `D^h u = (D_1^h u, …, D_n^h u)` of Definition 4.51; `‖D^h u‖_{Lᵖ}` is the
`Lᵖ` norm of this function. -/
noncomputable def diffQuotNorm {n : ℕ} (h : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ i : Fin n, (diffQuot i h u x) ^ 2)

/-- `Ω′ ⋐ Ω` (Hunter, p. 1): a nonempty open set `Ω′` is compactly contained in `Ω` if its closure
`Ω̄′` is compact and `Ω̄′ ⊂ Ω`. -/
def CompactlyContained {n : ℕ} (Ω' Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Ω'.Nonempty ∧ IsOpen Ω' ∧ IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω

end HunterPDE.Regularity
