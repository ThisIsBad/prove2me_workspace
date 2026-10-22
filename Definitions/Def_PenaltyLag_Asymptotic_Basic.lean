import Mathlib

namespace PenaltyLag.Asymptotic

open Filter Topology

/-- ℝ^m with the Euclidean norm |·| and the inner product u·y (indices `Fin m`, 0-based). -/
abbrev Mult (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- θ(t) = max{0, t} (1.2). -/
def theta (t : ℝ) : ℝ := max 0 t

/-- The penalty Lagrangian L_r (2.3). Meaningful for r > 0; every statement assumes it. -/
noncomputable def Lr {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (x : E)
    (y : Mult m) : ℝ :=
  f₀ x + (1 / (4 * r)) * ∑ i, (theta (y i + 2 * r * f i x) ^ 2 - y i ^ 2)

/-- The ordinary Lagrangian L₀ (3.2): f₀(x) + Σ yᵢ fᵢ(x) if y ≥ 0, −∞ otherwise. -/
noncomputable def L0 {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (x : E)
    (y : Mult m) : EReal :=
  if ∀ i, 0 ≤ y i then ((f₀ x + ∑ i, y i * f i x : ℝ) : EReal) else ⊥

/-- F_r (3.4): f₀(x) + r Σ uᵢ² if uᵢ ≥ fᵢ(x) for all i, +∞ otherwise. -/
noncomputable def Fr {E : Type*} {m : ℕ} (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (x : E)
    (u : Mult m) : EReal :=
  if ∀ i, f i x ≤ u i then ((f₀ x + r * ∑ i, u i ^ 2 : ℝ) : EReal) else ⊤

/-- g_r(y) = inf_{x ∈ X} L_r(x, y), the objective of (D_r), valued in [−∞, +∞]. -/
noncomputable def gr {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (y : Mult m) : EReal :=
  ⨅ x ∈ X, (Lr f₀ f r x y : EReal)

/-- g₀(y) = inf_{x ∈ X} L₀(x, y), the objective of the ordinary dual (D₀). -/
noncomputable def g0 {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (y : Mult m) : EReal :=
  ⨅ x ∈ X, L0 f₀ f x y

/-- g_r as a real function; used only where g_r is known to be finite (it is 0 at ±∞). -/
noncomputable def grR {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (y : Mult m) : ℝ :=
  (gr X f₀ f r y).toReal

/-- The dual optimal value sup_y g₀(y) (= sup_y g_r(y) for r > 0, Theorem 3.2). -/
noncomputable def dualValue {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) :
    EReal :=
  ⨆ y, g0 X f₀ f y

/-- A maximizing sequence for (D_r) (p. 364): g_r(yᵏ) → sup_y g_r(y) in [−∞, +∞]. -/
def IsMaximizing {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (y : ℕ → Mult m) : Prop :=
  Tendsto (fun k => gr X f₀ f r (y k)) atTop (𝓝 (⨆ y', gr X f₀ f r y'))

/-- Asymptotically feasible for (P) (4.5): xᵏ ∈ X and lim sup_k fᵢ(xᵏ) ≤ 0 for every i. -/
def IsAsympFeasible {E : Type*} {m : ℕ} (X : Set E) (f : Fin m → E → ℝ) (x : ℕ → E) : Prop :=
  (∀ k, x k ∈ X) ∧ ∀ i, limsup (fun k => (f i (x k) : EReal)) atTop ≤ 0

/-- The asymptotic optimal value in (P) (p. 364): the infimum of lim sup_k f₀(xᵏ) over all
asymptotically feasible sequences (+∞ if there are none). -/
noncomputable def asympValue {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ)
    (f : Fin m → E → ℝ) : EReal :=
  ⨅ (x : ℕ → E) (_ : IsAsympFeasible X f x), limsup (fun k => (f₀ (x k) : EReal)) atTop

/-- An asymptotically minimizing sequence for (P) (p. 364): asymptotically feasible, with
lim sup_k f₀(xᵏ) equal to the asymptotic optimal value. -/
def IsAsympMinimizing {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (x : ℕ → E) : Prop :=
  IsAsympFeasible X f x ∧ limsup (fun k => (f₀ (x k) : EReal)) atTop = asympValue X f₀ f

end PenaltyLag.Asymptotic
