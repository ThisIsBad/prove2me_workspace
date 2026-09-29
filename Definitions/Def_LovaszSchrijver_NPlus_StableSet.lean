import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_MatrixCone

namespace LovaszSchrijver.NPlus

/-- The incidence vector `χ^A ∈ ℝ^V` of a set `A ⊆ V`. -/
def chi {V : Type} [DecidableEq V] (A : Finset V) : V → ℝ :=
  fun i => if i ∈ A then 1 else 0

/-- `STAB(G) = conv{χ^A : A is stable}` (p. 175). -/
def STAB {V : Type} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ {x | ∃ A : Finset V, G.IsIndepSet (A : Set V) ∧ x = chi A}

/-- `FRAC(G)`: the solution set of (1) `xᵢ ≥ 0` for `i ∈ V` and (2) `xᵢ + xⱼ ≤ 1` for
`ij ∈ E` (p. 175). -/
def FRAC {V : Type} (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i j, G.Adj i j → x i + x j ≤ 1}

/-- `FR(G) ⊆ ℝ^{V ∪ {0}}`, given by the constraints `xᵢ ≥ 0` for `i ∈ V` and
`xᵢ + xⱼ ≤ x₀` for `ij ∈ E` (p. 177). Coordinate `none` is `x₀`. -/
def FR {V : Type} (G : SimpleGraph V) : Set (Option V → ℝ) :=
  {x | (∀ i, 0 ≤ x (some i)) ∧ ∀ i j, G.Adj i j → x (some i) + x (some j) ≤ x none}

/-- Homogenization `x ↦ (1, x)`: the vector with `x₀ = 1` and `xᵢ` for `i ∈ V`. -/
def hom {V : Type} (x : V → ℝ) : Option V → ℝ :=
  fun o => o.elim 1 x

/-- `N₊ʳ(G) = N₊ʳ(FR(G)) ∩ H₀` in the original coordinates (p. 177): the `x ∈ ℝ^V` with
`(1, x) ∈ N₊ʳ(FR(G))`. -/
def NplusG {V : Type} [Fintype V] [DecidableEq V] (r : ℕ) (G : SimpleGraph V) :
    Set (V → ℝ) :=
  {x | hom x ∈ NplusIter r (FR G)}

/-- The inequality `aᵀx ≤ b` is valid for `S`. -/
def Valid {V : Type} [Fintype V] (S : Set (V → ℝ)) (a : V → ℝ) (b : ℝ) : Prop :=
  ∀ x ∈ S, ∑ i, a i * x i ≤ b

/-- Coefficient vector of the contraction of node `v` (p. 177), written on the same graph:
the coefficients of `v` and of its neighbours are set to `0` (the right-hand side becomes
`b - a v`). -/
def contractCoeff {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (a : V → ℝ) (v : V) : V → ℝ :=
  fun w => if w = v ∨ G.Adj v w then 0 else a w

end LovaszSchrijver.NPlus
