import Mathlib

namespace ProjLikeRetr.Retractor

/-- §2.1, p. 3: the tangent space `T_M(x)` of `M ⊆ E` at `x`, as a linear subspace of `E`: the
span of the tangent cone of `M` at `x` (for a `C¹` submanifold the tangent cone is already this
subspace). -/
noncomputable def tangentSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (x : E) : Submodule ℝ E :=
  Submodule.span ℝ (tangentConeAt ℝ M x)

/-- §2.1, p. 3: the normal space `N_M(x)`, the orthogonal complement of `T_M(x)` in `E`. -/
noncomputable def normalSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (x : E) : Submodule ℝ E :=
  (tangentSpace M x)ᗮ

/-- §2.1, p. 3: the tangent bundle `TM = {(x, u) ∈ E × E : x ∈ M, u ∈ T_M(x)}`. -/
def tangentBundle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) : Set (E × E) :=
  {p | p.1 ∈ M ∧ p.2 ∈ tangentSpace M p.1}

/-- §2.1, p. 3: the normal bundle `NM = {(x, v) ∈ E × E : x ∈ M, v ∈ N_M(x)}`. -/
def normalBundle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) : Set (E × E) :=
  {p | p.1 ∈ M ∧ p.2 ∈ normalSpace M p.1}

end ProjLikeRetr.Retractor
