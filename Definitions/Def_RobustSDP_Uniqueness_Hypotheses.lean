import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model

open Matrix

namespace RobustSDP.Uniqueness

namespace SDPData

variable {m n p q : ℕ} (D : SDPData m n p q)

/-- Standing assumption of Eq. (1), p. 33: the matrices `F₀, …, F_m` are symmetric. -/
def Symmetric : Prop :=
  D.F0.IsSymm ∧ ∀ i, (D.Fs i).IsSymm

/-- Hypothesis H1 (p. 38), the Slater condition: (15) is strictly feasible,
`𝓕(x, τ) ≻ 0` for some `(x, τ)`. -/
def Slater : Prop :=
  ∃ (x : Fin m → ℝ) (τ : ℝ), (D.lmi x τ).PosDef

/-- Hypothesis H2 (p. 38), inf-compactness of (15) with objective `cᵀx`: every sublevel set
`{(x, τ) feasible | cᵀx ≤ M}` is bounded in `ℝ^m × ℝ`. -/
def InfCompact (c : Fin m → ℝ) : Prop :=
  ∀ M : ℝ, Bornology.IsBounded {y : (Fin m → ℝ) × ℝ | D.Feasible y ∧ c ⬝ᵥ y.1 ≤ M}

/-- Hypothesis H3(a) (p. 38): the nullspace of `λR₀ + ∑ xᵢRᵢ` is the same subspace `N` for every
`(λ, x) ≠ (0, 0)`, and `N` is not the whole space `ℝⁿ`. -/
def H3a : Prop :=
  ∃ N : Submodule ℝ (Fin n → ℝ), N ≠ ⊤ ∧
    ∀ (lam : ℝ) (x : Fin m → ℝ), (lam ≠ 0 ∨ x ≠ 0) →
      LinearMap.ker (Matrix.toLin' (D.pencil lam x)) = N

/-- Hypothesis H3(b) (p. 38): for every `x`, the stacked `(p+q) × n` matrix `[Lᵀ; R(x)]` has full
column rank, i.e. `ξ ↦ [Lᵀξ; R(x)ξ]` is injective. -/
def H3b : Prop :=
  ∀ x : Fin m → ℝ, Function.Injective (Matrix.fromRows D.Lᵀ (D.R x)).mulVec

/-- Squared Euclidean distance on `ℝ^m × ℝ = ℝ^{m+1}`: `‖y − y'‖² = ∑ᵢ (xᵢ − x'ᵢ)² + (τ − τ')²`. -/
def sqDist (y y' : (Fin m → ℝ) × ℝ) : ℝ :=
  ∑ i, (y.1 i - y'.1 i) ^ 2 + (y.2 - y'.2) ^ 2

/-- The quadratic growth condition (QGC, §4.3, p. 39) for (15) at a point `y⋆`: there are `α > 0`
and a Euclidean neighbourhood of radius `ε > 0` of `y⋆` in which every feasible `y` satisfies
`cᵀx ≥ cᵀx⋆ + α‖y − y⋆‖²`. -/
def QGC (c : Fin m → ℝ) (ystar : (Fin m → ℝ) × ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ y : (Fin m → ℝ) × ℝ, D.Feasible y →
    sqDist y ystar < ε ^ 2 → c ⬝ᵥ ystar.1 + α * sqDist y ystar ≤ c ⬝ᵥ y.1

end SDPData

end RobustSDP.Uniqueness
