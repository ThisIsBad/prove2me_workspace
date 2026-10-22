import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

namespace PenaltyLag.Exact

/-- inf in (P): the infimum of f₀ over the feasible set {x ∈ X : fᵢ(x) ≤ 0 ∀ i}
(+∞ if it is empty, −∞ if f₀ is unbounded below on it). -/
noncomputable def primalValue {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ)
    (f : Fin m → E → ℝ) : EReal :=
  ⨅ x ∈ X, ⨅ (_ : ∀ i, f i x ≤ 0), (f₀ x : EReal)

/-- x̄ is an optimal solution to (P): feasible, and f₀(x̄) ≤ f₀(x) for every feasible x. -/
def IsOptimal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (xbar : E) :
    Prop :=
  xbar ∈ X ∧ (∀ i, f i xbar ≤ 0) ∧ ∀ x ∈ X, (∀ i, f i x ≤ 0) → f₀ xbar ≤ f₀ x

/-- (P) is normal (p. 361): the dual optimal value equals the primal optimal value. -/
def IsNormal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) : Prop :=
  PenaltyLag.Asymptotic.dualValue X f₀ f = primalValue X f₀ f

/-- ȳ is an optimal solution to (D_r): g_r(ȳ) = sup_y g_r(y). By the convention of p. 361,
no dual optimal solution exists when g_r ≡ −∞; hence the clause g_r(ȳ) ≠ −∞. -/
def IsDualOptimal {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  PenaltyLag.Asymptotic.gr X f₀ f r ybar ≠ ⊥ ∧ PenaltyLag.Asymptotic.gr X f₀ f r ybar = ⨆ y, PenaltyLag.Asymptotic.gr X f₀ f r y

/-- ȳ is a Kuhn–Tucker vector for (P) relative to L_r, r > 0 (3.17):
−∞ < inf_{x ∈ X} L_r(x, ȳ) = inf in (P). -/
def IsKTVector {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  ⊥ < PenaltyLag.Asymptotic.gr X f₀ f r ybar ∧ PenaltyLag.Asymptotic.gr X f₀ f r ybar = primalValue X f₀ f

/-- ȳ is a Kuhn–Tucker vector for (P) relative to L₀ ((3.17) with L₀ in place of L_r). -/
def IsKTVector0 {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  ⊥ < PenaltyLag.Asymptotic.g0 X f₀ f ybar ∧ PenaltyLag.Asymptotic.g0 X f₀ f ybar = primalValue X f₀ f

/-- (x̄, ȳ) is a saddle point of L_r on X × ℝ^m (minimum in x over X, maximum in y over ℝ^m):
L_r(x̄, y) ≤ L_r(x̄, ȳ) ≤ L_r(x, ȳ) for all x ∈ X, y ∈ ℝ^m, with x̄ ∈ X. -/
def IsSaddle {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (xbar : E)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  xbar ∈ X ∧ (∀ y, PenaltyLag.Asymptotic.Lr f₀ f r xbar y ≤ PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar) ∧ ∀ x ∈ X, PenaltyLag.Asymptotic.Lr f₀ f r xbar ybar ≤ PenaltyLag.Asymptotic.Lr f₀ f r x ybar

/-- (x̄, ȳ) is a saddle point of the (extended-real valued) ordinary Lagrangian L₀ on X × ℝ^m. -/
def IsSaddle0 {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (xbar : E)
    (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  xbar ∈ X ∧ (∀ y, PenaltyLag.Asymptotic.L0 f₀ f xbar y ≤ PenaltyLag.Asymptotic.L0 f₀ f xbar ybar) ∧ ∀ x ∈ X, PenaltyLag.Asymptotic.L0 f₀ f xbar ybar ≤ PenaltyLag.Asymptotic.L0 f₀ f x ybar

/-- The ordinary Kuhn–Tucker conditions (i), (ii) of Corollary 3.4:
(i) ȳᵢ ≥ 0, fᵢ(x̄) ≤ 0, ȳᵢ fᵢ(x̄) = 0 for every i; (ii) x̄ ∈ X minimizes f₀ + Σ ȳᵢ fᵢ over X. -/
def KuhnTuckerConditions {E : Type*} {m : ℕ} (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (xbar : E) (ybar : PenaltyLag.Asymptotic.Mult m) : Prop :=
  (∀ i, 0 ≤ ybar i ∧ f i xbar ≤ 0 ∧ ybar i * f i xbar = 0) ∧
  xbar ∈ X ∧ ∀ x ∈ X, f₀ xbar + ∑ i, ybar i * f i xbar ≤ f₀ x + ∑ i, ybar i * f i x

end PenaltyLag.Exact
