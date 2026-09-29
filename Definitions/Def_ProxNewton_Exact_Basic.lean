import Mathlib

open scoped RealInnerProductSpace

namespace ProxNewton.Exact

/-! Objects of Lee, Sun & Saunders, *Proximal Newton-type methods for minimizing composite
functions*, arXiv:1206.1623v13: problem (1.1), §2.2 (search direction (2.9), λ (2.19),
Algorithm 1), Definition 3.2 and the Dennis–Moré criterion (3.2). The space is
`EuclideanSpace ℝ (Fin n)` (the paper's `ℝⁿ` with `⟨x, y⟩ = xᵀy`). -/

/-- The nonsmooth part `h` of (1.1) is a proper closed convex function that may take the value
`+∞`. It is encoded by its effective domain `D` and its (finite) values `h` on `D`: `D` is
nonempty and convex, `h` is convex on `D`, and the extended-valued function equal to `h` on `D`
and to `+∞` off `D` is lower semicontinuous (i.e. closed). Values of `h` off `D` are never read. -/
def IsProperClosedConvex {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  D.Nonempty ∧ Convex ℝ D ∧ ConvexOn ℝ D h ∧
    LowerSemicontinuous (fun x => by
      classical exact if x ∈ D then ((h x : ℝ) : EReal) else (⊤ : EReal))

/-- The composite objective `f = g + h` of problem (1.1), as an extended-valued function:
`f x = g x + h x` for `x ∈ D = dom f`, and `f x = +∞` otherwise. -/
noncomputable def compositeObj {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → EReal := fun x => by
  classical exact if x ∈ D then ((g x + h x : ℝ) : EReal) else (⊤ : EReal)

/-- `xstar` is an optimal solution of (1.1): it lies in `dom f = D` and
`f xstar ≤ f y` for every `y ∈ D`. -/
def IsMinimizer {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) : Prop :=
  xstar ∈ D ∧ ∀ y ∈ D, g xstar + h xstar ≤ g y + h y

/-- Definition 3.2, (3.1): `g` is strongly convex with constant `m`:
`g y ≥ g x + ∇g(x)ᵀ(y − x) + (m/2)‖x − y‖²` for all `x, y`. -/
def StronglyConvexWith {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℝ) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin n),
    g x + ⟪gradient g x, y - x⟫ + m / 2 * ‖x - y‖ ^ 2 ≤ g y

/-- The Hessian `∇²g(x)`, as the derivative of the gradient map, a linear operator on `ℝⁿ`. -/
noncomputable def hessian {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (gradient g) x

/-- `H` is a symmetric positive definite matrix: `H` is self-adjoint and `vᵀHv > 0` for `v ≠ 0`. -/
def IsPosDef {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric ∧
    ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < ⟪H v, v⟫

/-- `H ⪰ mI` for a symmetric `H`: `H` is self-adjoint and `m‖v‖² ≤ vᵀHv` for all `v`. -/
def IsLowerBounded {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (m : ℝ) : Prop :=
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric ∧
    ∀ v : EuclideanSpace ℝ (Fin n), m * ‖v‖ ^ 2 ≤ ⟪H v, v⟫

/-- `mI ⪯ H ⪯ MI` for a symmetric `H`: `H` is self-adjoint and
`m‖v‖² ≤ vᵀHv ≤ M‖v‖²` for all `v`. -/
def IsBoundedBetween {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (m M : ℝ) : Prop :=
  (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric ∧
    ∀ v : EuclideanSpace ℝ (Fin n), m * ‖v‖ ^ 2 ≤ ⟪H v, v⟫ ∧ ⟪H v, v⟫ ≤ M * ‖v‖ ^ 2

/-- Search direction (2.9): `Δ` minimizes the subproblem
`d ↦ ∇g(x)ᵀd + ½ dᵀHd + h(x + d)` over `{d | x + d ∈ D}` (the constant `g x` of the model
`ĝ` is dropped), and `x + Δ ∈ D`. -/
def IsSearchDirection {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : EuclideanSpace ℝ (Fin n)) : Prop :=
  x + Δ ∈ D ∧ ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ D →
    ⟪gradient g x, Δ⟫ + 1 / 2 * ⟪H Δ, Δ⟫ + h (x + Δ) ≤
      ⟪gradient g x, d⟫ + 1 / 2 * ⟪H d, d⟫ + h (x + d)

/-- The predicted decrease (2.19): `λ = ∇g(x)ᵀΔ + h(x + Δ) − h(x)`. -/
noncomputable def predDecrease {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (x Δ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪gradient g x, Δ⟫ + h (x + Δ) - h x

/-- The sufficient descent condition (2.19) for step length `t`:
`f(x + tΔ) ≤ f(x) + α t λ`, with `f` the extended-valued objective (so `x + tΔ ∈ D` is
part of the condition) and `f(x) = g x + h x` (used at points `x ∈ D`). -/
def SufficientDescent {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Prop :=
  compositeObj g D h (x + t • Δ) ≤ ((g x + h x + α * t * predDecrease g h x Δ : ℝ) : EReal)

/-- Backtracking line search with factor `β`: `t = β ^ j` where `j` is the least natural
number such that the step `β ^ j` satisfies the sufficient descent condition (2.19). The unit
step `β ^ 0 = 1` is tried first. -/
def IsBacktrackingStep {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α β : ℝ)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Prop :=
  ∃ j : ℕ, t = β ^ j ∧ SufficientDescent g D h α x Δ (β ^ j) ∧
    ∀ i : ℕ, i < j → ¬ SufficientDescent g D h α x Δ (β ^ i)

/-- A run of Algorithm 1 (generic proximal Newton-type method, p. 8) with sufficient-descent
parameter `α` and backtracking factor `β`: `x 0 ∈ D`, and for every `k`, `H k` is symmetric
positive definite, `Δ k` is the search direction (2.9) at `x k` with `H k`, `t k` is the
backtracking step, and `x (k+1) = x k + t k • Δ k`. The run is infinite (no stopping test). -/
def IsProxNewtonTypeRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) : Prop :=
  x 0 ∈ D ∧ ∀ k : ℕ, IsPosDef (H k) ∧ IsSearchDirection g D h (x k) (H k) (Δ k) ∧
    IsBacktrackingStep g D h α β (x k) (Δ k) (t k) ∧ x (k + 1) = x k + t k • Δ k

/-- A run of the proximal Newton method: a run of Algorithm 1 with `H k = ∇²g(x k)`. -/
def IsProxNewtonRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (α β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Δ : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) : Prop :=
  IsProxNewtonTypeRun g D h α β x H Δ t ∧ ∀ k : ℕ, H k = hessian g (x k)

/-- The Dennis–Moré criterion (3.2), division-free:
`‖(H k − ∇²g(xstar))(x (k+1) − x k)‖ / ‖x (k+1) − x k‖ → 0`, written as: for every `ε > 0`,
eventually `‖(H k − ∇²g(xstar))(x (k+1) − x k)‖ ≤ ε ‖x (k+1) − x k‖`. -/
def DennisMore {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop,
    ‖(H k - hessian g xstar) (x (k + 1) - x k)‖ ≤ ε * ‖x (k + 1) - x k‖

end ProxNewton.Exact
