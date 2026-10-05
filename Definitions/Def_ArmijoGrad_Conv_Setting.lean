import Mathlib

namespace ArmijoGrad.Conv

/-- The level set `S(x₀) = {x : f(x) ≤ f(x₀)}` (§1, p. 1). -/
def levelSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | f x ≤ f x0}

/-- "`f ∈ C¹` on `s`": `f` is (Fréchet) differentiable on `Eⁿ` at every point of `s`, and its
gradient `∇f` is continuous on `s`. -/
def IsC1On {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : Set (EuclideanSpace ℝ (Fin n))) :
    Prop :=
  (∀ x ∈ s, DifferentiableAt ℝ f x) ∧ ContinuousOn (gradient f) s

/-- Condition I (§1, p. 1): `x*` is the unique point with `f(x*) = inf_{Eⁿ} f`. -/
def ConditionI {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  (∀ y, f xstar ≤ f y) ∧ ∀ z, (∀ y, f z ≤ f y) → z = xstar

/-- Condition II at `x₀` (§1, p. 1): `f ∈ C¹` on `S(x₀)`, and for `x ∈ S(x₀)`,
`∇f(x) = 0` iff `x = x*`. -/
def ConditionII {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 xstar : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsC1On f (levelSet f x0) ∧ ∀ x ∈ levelSet f x0, (gradient f x = 0 ↔ x = xstar)

/-- Condition III at `x₀` (§1, p. 1): `f ∈ C¹` on `S(x₀)` and `∇f` is Lipschitz continuous on
`S(x₀)` with Lipschitz constant `K > 0`. -/
def ConditionIII {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n))
    (K : ℝ) : Prop :=
  0 < K ∧ IsC1On f (levelSet f x0) ∧
    ∀ x ∈ levelSet f x0, ∀ y ∈ levelSet f x0, ‖gradient f y - gradient f x‖ ≤ K * ‖y - x‖

/-- Condition IV at `x₀` (§1, p. 1), for the minimizer `x*`: `f ∈ C¹` on `S(x₀)`, `x*` minimizes
`f` over `Eⁿ`, and for every `r > 0`, `m(r) = inf {‖∇f(x)‖ : x ∈ S(x₀), ‖x - x*‖ ≥ r} > 0`
(with `m(r) = ∞` when that set is void), i.e. `‖∇f‖` has a positive lower bound on it. -/
def ConditionIV {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 xstar : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsC1On f (levelSet f x0) ∧ (∀ y, f xstar ≤ f y) ∧
    ∀ r : ℝ, 0 < r → ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ levelSet f x0, r ≤ ‖x - xstar‖ → m ≤ ‖gradient f x‖

/-- The set `S*(x, δ)` of display (1) (§2, p. 1):
`{x_λ : x_λ = x − λ∇f(x), λ > 0, f(x_λ) − f(x) ≤ −δ|∇f(x)|²}`. -/
def sdSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ t : ℝ, 0 < t ∧ y = x - t • gradient f x ∧ f y - f x ≤ -δ * ‖gradient f x‖ ^ 2}

/-- A run of the steepest descent algorithm of Corollary 1 (§2, p. 2):
`x_{k+1} = x_k − (1/2K)∇f(x_k)` for `k = 0, 1, 2, …`. -/
def IsSteepestDescentRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, x (k + 1) = x k - (1 / (2 * K)) • gradient f (x k)

/-- The step sizes `α_m = α / 2^{m−1}` of Corollary 2 (§2, p. 2); used only for `m ≥ 1`. -/
noncomputable def alphaSeq (α : ℝ) (m : ℕ) : ℝ :=
  α / 2 ^ (m - 1)

/-- Test (2) of Corollary 2 at the point `y` with index `m`:
`f(y − α_m∇f(y)) − f(y) ≤ −(1/2) α_m |∇f(y)|²`. -/
def armijoTest {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (m : ℕ) : Prop :=
  f (y - alphaSeq α m • gradient f y) - f y ≤ -(1 / 2) * alphaSeq α m * ‖gradient f y‖ ^ 2

/-- A run of the modified steepest descent algorithm of Corollary 2 (§2, p. 2):
`x_{k+1} = x_k − α_{m_k}∇f(x_k)`, where `m_k` is the smallest positive integer satisfying (2). -/
def IsModifiedSteepestDescentRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, ∃ m : ℕ, 1 ≤ m ∧ armijoTest f α (x k) m ∧
    (∀ j : ℕ, 1 ≤ j → j < m → ¬ armijoTest f α (x k) j) ∧
    x (k + 1) = x k - alphaSeq α m • gradient f (x k)

end ArmijoGrad.Conv
