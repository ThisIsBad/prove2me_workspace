import Mathlib

namespace LovaszSchrijver.NPlus

open Matrix

/-- The paper's polar cone `K* = {u : uᵀx ≥ 0 for all x ∈ K}` (p. 168). Coordinates of
`ℝ^{n+1}` are indexed by `Option ι`; `none` is the 0th coordinate `x₀`. -/
def dualCone {ι : Type} [Fintype ι] (K : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  {u | ∀ x ∈ K, 0 ≤ u ⬝ᵥ x}

/-- `K` is a convex cone: nonempty, closed under addition and under nonnegative scaling. -/
def IsConvexCone {ι : Type} (K : Set (Option ι → ℝ)) : Prop :=
  K.Nonempty ∧ (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧ ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K

/-- `cone S`: the convex cone spanned by `S` (all nonnegative combinations, `0` included). -/
def cone {ι : Type} (S : Set (Option ι → ℝ)) : Set (Option ι → ℝ) :=
  (PointedCone.hull ℝ S : Set (Option ι → ℝ))

/-- `x` is a 0–1 vector: every coordinate, `x₀` included, is `0` or `1`. -/
def IsZeroOne {ι : Type} (x : Option ι → ℝ) : Prop :=
  ∀ j, x j = 0 ∨ x j = 1

/-- `Q`: the cone spanned by all 0–1 vectors `x ∈ ℝ^{n+1}` with `x₀ = 1` (p. 169). -/
def Q {ι : Type} : Set (Option ι → ℝ) :=
  cone {x | IsZeroOne x ∧ x none = 1}

/-- The hyperplane `Gᵢ = {x : xᵢ = x₀}` (p. 171). -/
def G {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = x none}

/-- `M(K₁, K₂)` (p. 169): the symmetric `(n+1)×(n+1)` matrices `Y` with
(ii) `yᵢᵢ = y₀ᵢ` for `1 ≤ i ≤ n` and (iii) `uᵀYv ≥ 0` for every `u ∈ K₁*`, `v ∈ K₂*`. -/
def M {ι : Type} [Fintype ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Matrix (Option ι) (Option ι) ℝ) :=
  {Y | Y.IsSymm ∧ (∀ i : ι, Y (some i) (some i) = Y none (some i)) ∧
    ∀ u ∈ dualCone K₁, ∀ v ∈ dualCone K₂, 0 ≤ u ⬝ᵥ (Y *ᵥ v)}

/-- `M₊(K₁, K₂)` (p. 169): the matrices of `M(K₁, K₂)` that are (iv) positive semidefinite. -/
def Mplus {ι : Type} [Fintype ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Matrix (Option ι) (Option ι) ℝ) :=
  {Y | Y ∈ M K₁ K₂ ∧ Y.PosSemidef}

/-- `N₊(K₁, K₂) = {Ye₀ : Y ∈ M₊(K₁, K₂)}` (p. 169), `e₀ = Pi.single none 1`. -/
def Nplus {ι : Type} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  {x | ∃ Y ∈ Mplus K₁ K₂, Y *ᵥ Pi.single none 1 = x}

/-- `N₊(K) = N₊(K, Q)` (p. 170). -/
def N1plus {ι : Type} [Fintype ι] [DecidableEq ι] (K : Set (Option ι → ℝ)) :
    Set (Option ι → ℝ) :=
  Nplus K Q

/-- The iterates `N₊⁰(K) = K`, `N₊ᵗ(K) = N₊(N₊ᵗ⁻¹(K))` (p. 171, "and similarly for N₊"). -/
def NplusIter {ι : Type} [Fintype ι] [DecidableEq ι] :
    ℕ → Set (Option ι → ℝ) → Set (Option ι → ℝ)
  | 0, K => K
  | t + 1, K => N1plus (NplusIter t K)

end LovaszSchrijver.NPlus
