import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic
open Matrix

namespace LogRegretOCO.ONS

/-- The ONS step-size parameter `β = ½ min{1/(4GD), α}` (Fig. 2, p. 176). -/
noncomputable def onsBeta (G D α : ℝ) : ℝ := (1 / 2) * min (1 / (4 * G * D)) α

/-- The ONS regularisation parameter `ε = 1/(β²D²)` (Fig. 2, p. 176). -/
noncomputable def onsEps (G D α : ℝ) : ℝ := 1 / (onsBeta G D α ^ 2 * D ^ 2)

/-- The ONS matrix `A_t = Σ_{i=1}^t ∇_i ∇_iᵀ + ε Iₙ` with `∇_i = ∇f_i(x_i)` (Fig. 2, p. 176). -/
noncomputable def onsMatrix {n : ℕ} (G D α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  regGram (onsEps G D α) (fun i => gradient (f i) (x i)) t

/-- `x` is a run of the Online Newton Step (Fig. 2, p. 176) on the cost functions `f` over `P`
with parameters `G, D, α`: `x₁ ∈ P` is arbitrary, and for every round `t ≥ 1`
`x_{t+1}` is a generalized projection, in the norm induced by `A_t`, of
`y_{t+1} = x_t − (1/β) A_t⁻¹ ∇_t` onto `P` (the indexing of the proof on p. 177). -/
def IsONSRun {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (G D α : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 1 ∈ P ∧
    ∀ t : ℕ, 1 ≤ t →
      IsGenProj P (onsMatrix G D α f x t)
        (x t - (1 / onsBeta G D α) •
          WithLp.toLp 2 ((onsMatrix G D α f x t)⁻¹ *ᵥ WithLp.ofLp (gradient (f t) (x t))))
        (x (t + 1))

end LogRegretOCO.ONS
