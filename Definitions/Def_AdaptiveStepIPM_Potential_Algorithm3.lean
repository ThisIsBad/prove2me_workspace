import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Direction

/-!
Mizuno, Todd, Ye, Cornell ORIE TR 944 (1990, rev. 1991), §5 (p. 11), with the frame of
Algorithm 2 (§4, pp. 9–10).

The potential (1) `ψ(x, s) = ρ log(xᵀs) − Σⱼ log(x_j s_j)` is the published
`LinearOptimization.interiorPointPotential ρ x s = ρ log(sᵀx) − Σ log x_j − Σ log s_j`,
which agrees with (1) at every pair with `x, s > 0`; it is only ever evaluated at such pairs here.

Algorithm 3 is Algorithm 2 with `N = N_∞⁻(β)` except that the step `θ̄` is chosen so that
`(x(θ̄), s(θ̄)) ∈ N` and `ψ(x(θ̄), s(θ̄)) ≤ ψ(x(θ), s(θ))` for each `θ` with `(x(θ), s(θ)) ∈ N`.
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- The parameter of Theorem 3 (p. 11):
`ρ := n + (3/(βγ(1 − γ)) · log(1/(1 − β))) · n²`, with the natural logarithm. -/
noncomputable def rho (n : ℕ) (β γ : ℝ) : ℝ :=
  n + (3 / (β * γ * (1 - γ)) * Real.log (1 / (1 - β))) * (n : ℝ) ^ 2

/-- One iteration of Algorithm 3 (p. 11) from `(x, s)` to `(x', s')`: there is a solution
`d = (d_x, d_y, d_s)` of (2) at `(x, s)` with parameter `γ` and a step `θ̄` such that
`(x(θ̄), s(θ̄)) ∈ N_∞⁻(β)`, `ψ(x(θ̄), s(θ̄)) ≤ ψ(x(θ), s(θ))` for every real `θ` with
`(x(θ), s(θ)) ∈ N_∞⁻(β)`, and `(x', s') = (x(θ̄), s(θ̄))`. -/
def Alg3Step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (β γ ρ : ℝ) (x s x' s' : Fin n → ℝ) : Prop :=
  ∃ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (θbar : ℝ),
    IsNewtonDirection A γ x s dx dy ds ∧
    InNinfMinus A b c β (lineStep x dx θbar) (lineStep s ds θbar) ∧
    (∀ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) →
      LinearOptimization.interiorPointPotential ρ (lineStep x dx θbar) (lineStep s ds θbar) ≤
        LinearOptimization.interiorPointPotential ρ (lineStep x dx θ) (lineStep s ds θ)) ∧
    x' = lineStep x dx θbar ∧ s' = lineStep s ds θbar

/-- A run of Algorithm 3 with precision `t` (pp. 9–11): the iterates `(x^k, s^k)` start in
`N_∞⁻(β)` with `(x⁰)ᵀs⁰ ≤ 2^t` (Algorithm 2's "Given" clause) and
`ψ(x⁰, s⁰) ≤ (ρ − n)t + n log n` (§5), and while `(x^k)ᵀs^k > 2^{−t}` the next iterate is
produced by one iteration of Algorithm 3. Iterates after the loop stops are unconstrained. -/
def IsAlg3Run {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (β γ ρ t : ℝ) (x s : ℕ → Fin n → ℝ) : Prop :=
  InNinfMinus A b c β (x 0) (s 0) ∧
  x 0 ⬝ᵥ s 0 ≤ (2 : ℝ) ^ t ∧
  LinearOptimization.interiorPointPotential ρ (x 0) (s 0) ≤
    (ρ - n) * t + n * Real.log n ∧
  ∀ k : ℕ, (2 : ℝ) ^ (-t) < x k ⬝ᵥ s k →
    Alg3Step A b c β γ ρ (x k) (s k) (x (k + 1)) (s (k + 1))

end AdaptiveStepIPM.Potential
