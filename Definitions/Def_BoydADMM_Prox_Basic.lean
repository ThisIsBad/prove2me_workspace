import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection

namespace BoydADMM.Prox

/-! Objects of Chapter 4 of Boyd–Parikh–Chu–Peleato–Eckstein (2011), pp. 25–32.

Vectors live in `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is the Euclidean norm `‖·‖₂`. A matrix
`A ∈ ℝ^{p×n}` is `A : Matrix (Fin p) (Fin n) ℝ`, acting by `Matrix.toEuclideanLin A`.
An extended-real-valued `f : ℝⁿ → ℝ ∪ {+∞}` is encoded by its effective domain `C = dom f`
and its finite values `f` on `C`; the values of `f` outside `C` are never used. -/

/-- The ADMM `x`-update of Chapter 4 (p. 25):
`x⁺ = argmin_x (f(x) + (ρ/2)‖Ax − v‖₂²)`, where `f` has domain `C`.
`IsXUpdate C f ρ A v x` says that `x ∈ C` and `x` minimizes `f(x) + (ρ/2)‖Ax − v‖₂²` over `C`. -/
def IsXUpdate {n p : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ρ : ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ C ∧ ∀ x' ∈ C,
    f x + (ρ / 2) * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 ≤
      f x' + (ρ / 2) * ‖Matrix.toEuclideanLin A x' - v‖ ^ 2

/-- The proximity operator `prox_{f,ρ}(v)` of §4.1 (p. 25), the case `A = I` of the `x`-update:
`IsProx C f ρ v x` says that `x ∈ C` and `x` minimizes `f(x) + (ρ/2)‖x − v‖₂²` over `C = dom f`. -/
def IsProx {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ) (v x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ C ∧ ∀ x' ∈ C, f x + (ρ / 2) * ‖x - v‖ ^ 2 ≤ f x' + (ρ / 2) * ‖x' - v‖ ^ 2

/-- `x` is a Euclidean projection `Π_C(v)` of `v` onto `C` (p. 26). This is the
published nearest-point predicate, specialized to Boyd et al.'s finite-dimensional space. -/
abbrev IsProjection {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (v x : EuclideanSpace ℝ (Fin n)) : Prop :=
  RandomGradFree.Nonsmooth.IsMetricProjection C v x

/-- The nonnegative orthant `ℝⁿ₊ = {x | x_i ≥ 0 for all i}` (p. 26). -/
def nonnegOrthant (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, 0 ≤ x i}

/-- `(v)₊`, the vector of nonnegative parts `max(v_i, 0)` of the components of `v` (p. 26). -/
noncomputable def posPartVec {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => max (v i) 0)

/-- The quadratic formula of §4.2 (p. 26), `f(x) = (1/2)xᵀPx + qᵀx + r`.
The book's quadratic is convex when `P` is symmetric positive semidefinite; statements
about that setting assume `P.PosSemidef`. -/
noncomputable def quadObj {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (q : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2) * inner ℝ x (Matrix.toEuclideanLin P x) + inner ℝ q x + r

/-- The affine set `{x | Fx = g}` (§4.2.5, p. 29). -/
def affineSet {n m : ℕ} (F : Matrix (Fin m) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | Matrix.toEuclideanLin F x = g}

/-- The ℓ1 norm `‖x‖₁ = ∑ᵢ |x_i|` (§4.4.3, p. 32). -/
noncomputable def l1Norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, |x i|

/-- The soft thresholding operator `S_κ(a)` (§4.4.3, p. 32), in the book's three-case form:
`a − κ` if `a > κ`, `0` if `|a| ≤ κ`, `a + κ` if `a < −κ`. -/
noncomputable def softThreshold (κ a : ℝ) : ℝ :=
  if κ < a then a - κ else if a < -κ then a + κ else 0

/-- Componentwise soft thresholding of a vector, `(S_κ(v_1), …, S_κ(v_n))` (§4.4.3, p. 32). -/
noncomputable def softThresholdVec {n : ℕ} (κ : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => softThreshold κ (v i))

end BoydADMM.Prox
