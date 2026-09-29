import Mathlib

open MeasureTheory

namespace HighDimProb.Deviations

/-- **`IsIsotropic P X`**: the random vector `X : Ω → EuclideanSpace ℝ (Fin n)` is isotropic on
the probability space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition
3.2.1, p. 47 (PDF p. 55): "A random vector `X` in `ℝⁿ` is called isotropic if `Σ(X) = E[XXᵀ] =
Iₙ`." Formalized via the book's own basis-free equivalent, Lemma 3.2.3, p. 47/48 (PDF p. 55/56):
"`X` is isotropic if and only if `E⟨X,x⟩² = ‖x‖₂²` for all `x ∈ ℝⁿ`" — equal by the standard fact
that two symmetric matrices `A, B` agree iff `xᵀAx = xᵀBx` for every `x`, applied to `A = Σ(X)`,
`B = Iₙ`. The `Integrable` conjunct is essential for the same reason as in `subgaussianNorm`:
Mathlib's Bochner integral of a non-integrable function is `0` by convention, so without it a
non-integrable `⟨X,x⟩²` would vacuously satisfy the equation whenever `‖x‖² = 0`, i.e. at `x = 0`
only — harmless there, but the conjunct is kept uniformly for every `x` to make integrability of
every one-dimensional marginal `⟨X,x⟩` an explicit, checkable part of isotropy rather than a
silent side hypothesis needed later. -/
def IsIsotropic {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    Integrable (fun ω => (inner (𝕜 := ℝ) (X ω) x) ^ 2) P ∧
    ∫ ω, (inner (𝕜 := ℝ) (X ω) x) ^ 2 ∂P = ‖x‖ ^ 2

end HighDimProb.Deviations
