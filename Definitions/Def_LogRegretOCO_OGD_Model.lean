import Mathlib

namespace LogRegretOCO.OGD

/-- Points of the decision space: `ℝⁿ` with the Euclidean norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `IsProj P y z`: `z` is the Euclidean projection of `y` onto `P`,
`z = Π_P(y) = argmin_{x ∈ P} ‖x − y‖₂` (Fig. 1, p. 174). For a nonempty closed convex `P`
exactly one such `z` exists. -/
def IsProj {n : ℕ} (P : Set (E n)) (y z : E n) : Prop :=
  z ∈ P ∧ ∀ w ∈ P, ‖z - y‖ ≤ ‖w - y‖

/-- `IsHStrongConvex P H f` (§2.2, p. 172): `f` is twice differentiable and its Hessian is
bounded below by `H I_n` at every point of `P`, i.e. `∇²f(x) ⪰ H I_n` for `x ∈ P`, written as
`vᵀ ∇²f(x) v ≥ H ‖v‖²` for every `v`, with `∇²f(x)` the second Fréchet derivative. -/
def IsHStrongConvex {n : ℕ} (P : Set (E n)) (H : ℝ) (f : E n → ℝ) : Prop :=
  Differentiable ℝ f ∧ (∀ x ∈ P, DifferentiableAt ℝ (fderiv ℝ f) x) ∧
    ∀ x ∈ P, ∀ v : E n, H * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v

/-- `IsOGDRun P η f x` (Fig. 1, p. 174): `x` is a run of ONLINE GRADIENT DESCENT on the convex
set `P` with step sizes `η 1, η 2, …` against the cost functions `f 1, f 2, …`. Rounds are
1-based (`x 0`, `f 0` and `η 1` are never used): `x 1 ∈ P` is arbitrary, and in iteration
`t + 1 > 1` the point is `x (t + 1) = Π_P(x t − η (t + 1) ∇f_t(x t))`. -/
def IsOGDRun {n : ℕ} (P : Set (E n)) (η : ℕ → ℝ) (f : ℕ → E n → ℝ) (x : ℕ → E n) : Prop :=
  x 1 ∈ P ∧ ∀ t : ℕ, 1 ≤ t → IsProj P (x t - η (t + 1) • gradient (f t) (x t)) (x (t + 1))

end LogRegretOCO.OGD
