import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone

namespace LovaszSchrijver.OddHole

/-- `FRAC(G)` (p. 175): the solution set of `xᵢ ≥ 0` (i ∈ V) and `xᵢ + xⱼ ≤ 1` (ij ∈ E). -/
def FRAC {V : Type} (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i j, G.Adj i j → x i + x j ≤ 1}

/-- `FR(G)` (p. 177), given by its constraints: `xᵢ ≥ 0` for `i ∈ V` and
`xᵢ + xⱼ ≤ x₀` for `ij ∈ E`. Coordinates are `Option V`, with `none` the coordinate `x₀`. -/
def FR {V : Type} (G : SimpleGraph V) : Set (Option V → ℝ) :=
  {x | (∀ i, 0 ≤ x (some i)) ∧ ∀ i j, G.Adj i j → x (some i) + x (some j) ≤ x none}

/-- Homogenization `x ↦ (1, x)`: the vector of `ℝ^{V ∪ {0}}` with `x₀ = 1`. -/
def hom {V : Type} (x : V → ℝ) : Option V → ℝ :=
  fun o => o.elim 1 x

/-- `N(G) = N(FRAC(G)) = N(FR(G)) ∩ H₀`, read in the original space `ℝ^V` (p. 177). -/
def NG {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | hom x ∈ N (FR G)}

/-- The inequality `aᵀx ≤ b` is valid for `S ⊆ ℝ^V`. -/
def Valid {V : Type} [Fintype V] (S : Set (V → ℝ)) (a : V → ℝ) (b : ℝ) : Prop :=
  ∀ x ∈ S, ∑ i, a i * x i ≤ b

end LovaszSchrijver.OddHole
