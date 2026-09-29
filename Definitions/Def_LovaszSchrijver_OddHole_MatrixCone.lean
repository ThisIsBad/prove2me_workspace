import Mathlib

namespace LovaszSchrijver.OddHole

/-- A convex cone: a nonempty set closed under addition and under nonnegative scaling
(so it contains `0`). -/
def IsConvexCone {E : Type} [AddCommMonoid E] [SMul ℝ E] (K : Set E) : Prop :=
  K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧ ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K

/-- The polar (dual) cone `K* = {u : uᵀx ≥ 0 for all x ∈ K}` (p. 168). Coordinates of
`ℝ^{n+1}` are indexed by `Option ι`, with `none` the special 0th coordinate. -/
def dualCone {ι : Type} [Fintype ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  {u | ∀ x ∈ K, 0 ≤ dotProduct u x}

/-- `Q`: the cone spanned by all 0–1 vectors `x ∈ ℝ^{n+1}` with `x₀ = 1` (p. 169). -/
def Q (ι : Type) : Set (Option ι → ℝ) :=
  (PointedCone.hull ℝ {x : Option ι → ℝ | x none = 1 ∧ ∀ i : ι, x (some i) = 0 ∨ x (some i) = 1} :
    Set (Option ι → ℝ))

/-- The matrix cone `M(K₁, K₂)` (p. 169): the `(n+1) × (n+1)` matrices `Y` with
(i) `Y` symmetric, (ii) `yᵢᵢ = y₀ᵢ` for all `1 ≤ i ≤ n`, (iii) `uᵀYv ≥ 0` for every
`u ∈ K₁*` and `v ∈ K₂*`. -/
def M {ι : Type} [Fintype ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Matrix (Option ι) (Option ι) ℝ) :=
  {Y | Y.IsSymm ∧ (∀ i : ι, Y (some i) (some i) = Y none (some i)) ∧
    ∀ u ∈ dualCone K₁, ∀ v ∈ dualCone K₂, 0 ≤ dotProduct u (Y.mulVec v)}

/-- The projection `N(K₁, K₂) = {Y e₀ : Y ∈ M(K₁, K₂)}` (p. 169). -/
def Npair {ι : Type} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  {x | ∃ Y ∈ M K₁ K₂, Y.mulVec (Pi.single none 1 : Option ι → ℝ) = x}

/-- `N(K) = N(K, Q)` (p. 170). -/
def N {ι : Type} [Fintype ι] [DecidableEq ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  Npair K (Q ι)

end LovaszSchrijver.OddHole
