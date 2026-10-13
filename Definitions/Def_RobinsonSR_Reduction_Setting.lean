import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Reduction

open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normal-cone operator `∂ψ_C` (Robinson 1980, §1, p. 43), with `ℝⁿ` identified with its dual
through the inner product: for `x ∈ C` it is `{y | ⟪y, c - x⟫ ≤ 0 for all c ∈ C}`; for `x ∉ C` it
is `∅`. -/
def normalCone (C : Set E) (x : E) : Set E :=
  {y | x ∈ C ∧ ∀ c ∈ C, ⟪y, c - x⟫ ≤ 0}

/-- A polyhedral convex set: the intersection of finitely many closed half-spaces
`{x | ⟪a i, x⟫ ≤ b i}` (`m = 0` gives the whole space). -/
def IsPolyhedral (C : Set E) : Prop :=
  ∃ (m : ℕ) (a : Fin m → E) (b : Fin m → ℝ), C = {x | ∀ i, ⟪a i, x⟫ ≤ b i}

/-- The polar `S° = {h | ⟪y, h⟫ ≤ 0 for all y ∈ S}`. -/
def polar (S : Set E) : Set E :=
  {h | ∀ y ∈ S, ⟪y, h⟫ ≤ 0}

/-- The tangent cone `T_C(x₀) := ∂ψ_C(x₀)°` (Appendix, p. 58), the polar of the normal cone. -/
def tangentCone (C : Set E) (x0 : E) : Set E :=
  polar (normalCone C x0)

/-- The face `F := ∂ψ*_C(-y₀)` (Proposition A.2, p. 58): the subdifferential at `-y₀` of the
support function `ψ*_C` of `C`, i.e. the set of maximisers of `⟪-y₀, ·⟫` over `C`. It is `∅` when
the supremum is not attained. -/
def exposedFace (C : Set E) (y0 : E) : Set E :=
  {x | x ∈ C ∧ ∀ c ∈ C, ⟪-y0, c⟫ ≤ ⟪-y0, x⟫}

/-- The subspace parallel to a set `F`: the direction of its affine hull (Proposition A.3, p. 58). -/
def parallelSubspace (F : Set E) : Submodule ℝ E :=
  (affineSpan ℝ F).direction

/-- The lineality space of a cone `T` (p. 59): the subspace spanned by `T ∩ (-T)` (for a convex
cone `T`, `T ∩ (-T)` is already this subspace). -/
def linealitySpace (T : Set E) : Submodule ℝ E :=
  Submodule.span ℝ (T ∩ -T)

/-- Strong regularity (DEFINITION, p. 45) of the linear generalized equation
`0 ∈ A x + a + ∂ψ_C(x)` (A.1) at `x₀`, with associated Lipschitz constant `lam`. Here
`f(x) = A x + a`, so `f(x₀) + f′(x₀)(x - x₀) = A x + a` and `T x = A x + a + ∂ψ_C(x)`. There are
the required condition that `x₀` solves the unperturbed equation, and neighbourhoods `U` of `0`
and `V` of `x₀` such that the restriction to `U` of `T⁻¹ ∩ V` is a
single-valued function `s : U → V`, Lipschitzian on `U` with modulus `lam`: for each `y ∈ U`,
`s y ∈ V` solves `y ∈ T (s y)` (the inclusion (A.2)), it is the only solution in `V`, and
`‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖` on `U`. -/
def StronglyRegularLin {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : Prop :=
  -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0 ∧
  ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ V ∈ 𝓝 x0,
    ∃ s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      (∀ y ∈ U, s y ∈ V ∧ y - (Matrix.toEuclideanLin A (s y) + a) ∈ normalCone C (s y) ∧
         ∀ x ∈ V, y - (Matrix.toEuclideanLin A x + a) ∈ normalCone C x → x = s y) ∧
      ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖

end RobinsonSR.Reduction
