import Mathlib
import Definitions.Def_PathFindingLP_Centering_SlackSensitivity

open Matrix

namespace PathFindingLP.Centering

variable {m n : ℕ}

/-- The weighted norm `‖y‖_{G} = √(∑ᵢ gᵢ yᵢ²)` of `G = diag(g)`. -/
noncomputable def diagNorm {k : ℕ} (g y : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, g i * y i ^ 2)

/-- The vector `G(s)⁻¹ G'(s) S y`, where `G(s) = diag(g(s))`, `G'(s) = J_s(g(s))` is the Jacobian
of `g` at `s` (the Fréchet derivative `fderiv ℝ g s`), and `S = diag(s)`. -/
noncomputable def jacobianTerm (g : (Fin m → ℝ) → (Fin m → ℝ)) (s y : Fin m → ℝ) :
    Fin m → ℝ :=
  fun i => (g s i)⁻¹ * fderiv ℝ g s (fun j => s j * y j) i

/-- Definition 4 (Weight Function), §IV.C, p. 428, relative to the constraint matrix `A`.
`g : ℝᵐ_{>0} → ℝᵐ_{>0}` is differentiable, and for constants `c₁, c_γ, c_r` and all
`s ∈ ℝᵐ_{>0}`:
* Size: `‖g(s)‖₁ ≤ c₁` (read as an upper bound, see the natural-language statement);
* Slack Sensitivity: `c_γ ≥ 1` and `γ(s, g(s)) ≤ c_γ`;
* Step Consistency: `c_r ≥ 1` and for all `r ≥ c_r` and all `y ∈ ℝᵐ`,
  `‖(I + r⁻¹ G(s)⁻¹ G'(s) S) y‖_{G(s)} ≤ ‖y‖_{G(s)}` and
  `‖y + r⁻¹ G(s)⁻¹ G'(s) S y‖_∞ ≤ ‖y‖_∞ + c_r ‖y‖_{G(s)}`;
* Uniformity: `‖g(s)‖_∞ ≤ 2`.
Here `‖·‖_∞` on `Fin m → ℝ` is Mathlib's sup norm `‖·‖`. -/
structure IsWeightFunction (A : Matrix (Fin m) (Fin n) ℝ) (g : (Fin m → ℝ) → (Fin m → ℝ))
    (c₁ cγ cr : ℝ) : Prop where
  pos : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∀ i, 0 < g s i
  differentiableAt : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → DifferentiableAt ℝ g s
  size : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∑ i, |g s i| ≤ c₁
  one_le_cγ : 1 ≤ cγ
  slackSensitivity_le : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → slackSensitivity A s (g s) ≤ cγ
  one_le_cr : 1 ≤ cr
  stepConsistency_op : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∀ r : ℝ, cr ≤ r → ∀ y : Fin m → ℝ,
    diagNorm (g s) (y + r⁻¹ • jacobianTerm g s y) ≤ diagNorm (g s) y
  stepConsistency_inf : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∀ r : ℝ, cr ≤ r → ∀ y : Fin m → ℝ,
    ‖y + r⁻¹ • jacobianTerm g s y‖ ≤ ‖y‖ + cr * diagNorm (g s) y
  uniformity : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ‖g s‖ ≤ 2

end PathFindingLP.Centering
