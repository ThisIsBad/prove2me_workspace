import Mathlib

namespace RobustGeneralization.GaussLower

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The feature space `ℝ^d`, with its Euclidean structure and Borel σ-algebra. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The ℓ∞ perturbation set `B∞^ε(x) = {x' ∈ ℝ^d | ‖x' − x‖∞ ≤ ε}` (Schmidt et al., arXiv:1804.11285v2,
p. 5, after Definition 3), written coordinatewise: `E d` carries the ℓ2 norm, so
`Metric.closedBall` would be the ℓ2 ball. -/
def linfBall {d : ℕ} (x : E d) (ε : ℝ) : Set (E d) :=
  {x' | ∀ i, |x' i - x i| ≤ ε}

/-- The Gaussian `N(m, s²I)` on `ℝ^d`: the law of `m + s • v` for `v` standard Gaussian.
`s` is the standard deviation. -/
noncomputable def gaussVec {d : ℕ} (m : E d) (s : ℝ) : Measure (E d) :=
  (stdGaussian (E d)).map (fun v => m + s • v)

/-- The `(θ⋆, σ)`-Gaussian model (Definition 1, p. 4): the label `y ∈ {±1}` is uniform
(`true` = +1, `false` = −1) and, given `y`, `x ∼ N(y · θ⋆, σ²I)`. The measure is the joint
law of `(x, y)` on `ℝ^d × {±1}`. -/
noncomputable def gaussModel {d : ℕ} (θ : E d) (σ : ℝ) : Measure (E d × Bool) :=
  (1 / 2 : ℝ≥0∞) • (gaussVec θ σ).map (fun x => (x, true)) +
    (1 / 2 : ℝ≥0∞) • (gaussVec (-θ) σ).map (fun x => (x, false))

/-- The `ℓ∞^ε`-robust classification error of a classifier `f : ℝ^d → {±1}` under a
distribution `P` on `ℝ^d × {±1}` (Definition 3, p. 5, with `B = B∞^ε`):
`P_{(x,y)∼P}[∃ x' ∈ B∞^ε(x) : f(x') ≠ y]`. For a non-measurable event this is the outer
measure, i.e. the probability under the completion of `P`. -/
noncomputable def robustErr {d : ℕ} (P : Measure (E d × Bool)) (f : E d → Bool) (ε : ℝ) : ℝ≥0∞ :=
  P {p | ∃ x' ∈ linfBall p.1 ε, f x' ≠ p.2}

/-- The expected `ℓ∞^ε`-robust classification error `Ξ` of a learning algorithm
`g` on `n` samples (§A.2, proof of Theorem 11, p. 28): draw `θ ∼ N(0, I)`, then `n` i.i.d.
samples `S` from the `(θ, σ)`-Gaussian model, and average the robust error of `f_n = g S`
under the same model. The learner sees only `S`, never `θ`. -/
noncomputable def expRobErr {d n : ℕ} (g : (Fin n → E d × Bool) → E d → Bool) (σ ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ∫⁻ S, robustErr (gaussModel θ σ) (g S) ε
      ∂(Measure.pi fun _ : Fin n => gaussModel θ σ) ∂(stdGaussian (E d))

/-- The marginal law `M` of `(z_1, …, z_n)` (§A.2, p. 28), where `θ ∼ N(0, I)` and, given `θ`,
the `z_i` are i.i.d. `N(θ, σ²I)`. -/
noncomputable def sampleMarginal (d n : ℕ) (σ : ℝ) : Measure (Fin n → E d) :=
  (stdGaussian (E d)).bind (fun θ => Measure.pi fun _ : Fin n => gaussVec θ σ)

/-- The posterior of `θ` given `z_1, …, z_n` (§A.2, p. 28): `N(µ′, Σ′)` with
`µ′ = (σ² + n)⁻¹ ∑_i z_i` (that is, `n/(σ²+n)` times the sample mean) and
`Σ′ = σ²/(σ²+n) I`, i.e. standard deviation `σ / √(σ² + n)`. -/
noncomputable def posterior {d n : ℕ} (z : Fin n → E d) (σ : ℝ) : Measure (E d) :=
  gaussVec ((σ ^ 2 + n)⁻¹ • ∑ i, z i) (σ / Real.sqrt (σ ^ 2 + n))

end RobustGeneralization.GaussLower
