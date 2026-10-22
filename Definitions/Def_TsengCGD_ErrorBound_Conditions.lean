import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic

namespace TsengCGD.ErrorBound

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The objective of (42) at (d, δ): ∇f(x)ᵀd + ½‖d‖² + ½δ² + cδ. -/
noncomputable def epiObj (f : TsengCGD.Global.Vec n → ℝ) (c : ℝ) (x d : TsengCGD.Global.Vec n) (δ : ℝ) : ℝ :=
  ⟪gradient f x, d⟫ + ‖d‖ ^ 2 / 2 + δ ^ 2 / 2 + c * δ

/-- (d, δ) is an optimal solution of (42) at (x, ξ): (x + d, ξ + δ) ∈ epi P, i.e. x + d ∈ dom P and
P(x + d) ≤ ξ + δ, and no feasible (d′, δ′) has a smaller objective. -/
def IsEpiSubSol (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ) (x : TsengCGD.Global.Vec n) (ξ : ℝ)
    (d : TsengCGD.Global.Vec n) (δ : ℝ) : Prop :=
  x + d ∈ D ∧ P (x + d) ≤ ξ + δ ∧
    ∀ (d' : TsengCGD.Global.Vec n) (δ' : ℝ), x + d' ∈ D → P (x + d') ≤ ξ + δ' →
      epiObj f c x d δ ≤ epiObj f c x d' δ'

/-- ‖(d, δ)‖, the Euclidean norm on ℜⁿ × ℜ. -/
noncomputable def pairNorm (d : TsengCGD.Global.Vec n) (δ : ℝ) : ℝ := Real.sqrt (‖d‖ ^ 2 + δ ^ 2)

/-- P is Lipschitz continuous on dom P with constant K ≥ 0. -/
def PLipOn (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ y ∈ D, ∀ z ∈ D, |P y - P z| ≤ K * ‖y - z‖

/-- P is polyhedral (p. 388): its epigraph epi P = {(x, ξ) | x ∈ D, P x ≤ ξ} is a polyhedral set,
i.e. the solution set of finitely many weak linear inequalities in (x, ξ) ∈ ℜⁿ × ℜ. -/
def IsPolyhedral (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → TsengCGD.Global.Vec n) (b e : Fin m → ℝ),
    ∀ (x : TsengCGD.Global.Vec n) (ξ : ℝ), (x ∈ D ∧ P x ≤ ξ) ↔ ∀ i, ⟪a i, x⟫ + b i * ξ ≤ e i

/-- A polyhedral set in ℜᵐ: the solution set of finitely many weak linear inequalities. -/
def IsPolyhedralSet {m : ℕ} (Y : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∃ (r : ℕ) (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ),
    Y = {y | ∀ i, ⟪a i, y⟫ ≤ b i}

/-- f is quadratic: f(x) = ½xᵀAx + bᵀx + c₀ for all x, with A symmetric (not necessarily
positive semidefinite). -/
def IsQuadratic (f : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : TsengCGD.Global.Vec n) (c₀ : ℝ),
    A.IsSymm ∧ ∀ x, f x = TsengCGD.Global.qf A x / 2 + ⟪b, x⟫ + c₀

/-- Condition C1 of Lemma 7 (p. 411): f is quadratic and P is polyhedral. -/
def C1 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  IsQuadratic f ∧ IsPolyhedral D P

/-- Condition C2 of Lemma 7 (p. 411): f(x) = g(Ex) + qᵀx for all x, with E : ℜⁿ → ℜᵐ linear,
q ∈ ℜⁿ, g strongly convex and differentiable on ℜᵐ with ∇g Lipschitz on ℜᵐ; P is polyhedral. -/
def C2 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (m : ℕ) (E : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (q : TsengCGD.Global.Vec n)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (μ : ℝ) (Lg : NNReal),
    0 < μ ∧ StrongConvexOn Set.univ μ g ∧ Differentiable ℝ g ∧
      LipschitzWith Lg (gradient g) ∧ (∀ x, f x = g (E x) + ⟪q, x⟫) ∧ IsPolyhedral D P

/-- Condition C3 of Lemma 7 (p. 411): f(x) = max_{y∈Y} {(Ex)ᵀy − g(y)} + qᵀx for all x, the maximum
being attained, with Y ⊆ ℜᵐ polyhedral, E : ℜⁿ → ℜᵐ linear, q ∈ ℜⁿ, g strongly convex and
differentiable on ℜᵐ with ∇g Lipschitz on ℜᵐ; P is polyhedral. -/
def C3 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) : Prop :=
  ∃ (m : ℕ) (Y : Set (EuclideanSpace ℝ (Fin m)))
    (E : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (q : TsengCGD.Global.Vec n)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (μ : ℝ) (Lg : NNReal),
    IsPolyhedralSet Y ∧ 0 < μ ∧ StrongConvexOn Set.univ μ g ∧ Differentiable ℝ g ∧
      LipschitzWith Lg (gradient g) ∧
      (∀ x, IsGreatest {v | ∃ y ∈ Y, v = ⟪E x, y⟫ - g y} (f x - ⟪q, x⟫)) ∧ IsPolyhedral D P

/-- Condition C4 of Theorem 4 (p. 412): f is strongly convex (on dom P) and satisfies (22) for some
L ≥ 0. -/
def C4 (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) : Prop :=
  (∃ μ > 0, StrongConvexOn D μ f) ∧ ∃ L, TsengCGD.Linear.GradLipOn f D L

end TsengCGD.ErrorBound
