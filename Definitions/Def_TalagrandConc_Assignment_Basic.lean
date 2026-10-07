import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.Assignment

open MeasureTheory

/-- Talagrand (1995), p. 166: for a digraph `D ⊆ I × J` and `S ⊆ I`,
`D(S) = { j ∈ J ; ∃ i ∈ S, (i, j) ∈ D }`. Here `I = J = Fin N`. -/
def nbhd {N : ℕ} (D : Set (Fin N × Fin N)) (S : Set (Fin N)) : Set (Fin N) :=
  {j | ∃ i ∈ S, (i, j) ∈ D}

/-- Talagrand (1995), p. 166, Eqs. (10.1)–(10.2): a digraph `D ⊆ I × J` (`I = J = Fin N`) is
`α`-expanding (`α ≥ 2`) if for all subsets `S` of `I`,
`card S ≤ N/2 ⇒ card D(S) ≥ min(α card S, N/2)` and
`card S ≥ N/2 ⇒ card D(S) ≥ N − (1/α)(N − card S)`.
The requirement `α ≥ 2` is part of the definition. Cardinalities of subsets of the finite
type `Fin N` are computed with `Set.ncard` (no junk value: every such set is finite). -/
def IsExpanding (N : ℕ) (α : ℝ) (D : Set (Fin N × Fin N)) : Prop :=
  2 ≤ α ∧ ∀ S : Set (Fin N),
    ((S.ncard : ℝ) ≤ (N : ℝ) / 2 →
        min (α * S.ncard) ((N : ℝ) / 2) ≤ ((nbhd D S).ncard : ℝ)) ∧
    ((N : ℝ) / 2 ≤ S.ncard →
        (N : ℝ) - (1 / α) * ((N : ℝ) - S.ncard) ≤ ((nbhd D S).ncard : ℝ))

/-- Talagrand (1995), p. 166: the cost `∑_{i ∈ I} a_{i, τ(i)}` of the assignment `τ`
(a one-to-one map from `I` onto `J`, here a permutation of `Fin N`) for the cost matrix
`a : I × J → ℝ`. -/
def assignmentCost {N : ℕ} (a : Fin N × Fin N → ℝ) (τ : Equiv.Perm (Fin N)) : ℝ :=
  ∑ i, a (i, τ i)

/-- Talagrand (1995), p. 166: the optimal assignment cost
`L_N = inf { ∑_{i ∈ I} a_{i, τ(i)} ; τ assignment }`, a minimum over the finite nonempty set
of permutations of `Fin N`. -/
def optCost {N : ℕ} (a : Fin N × Fin N → ℝ) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin N))).inf' Finset.univ_nonempty
    (fun τ => assignmentCost a τ)

/-- An optimal assignment for the cost matrix `a`: a permutation `τ` of minimal cost
(Talagrand (1995), p. 167, Corollary 10.2, "an optimal assignment τ"). -/
def IsOptimalAssignment {N : ℕ} (a : Fin N × Fin N → ℝ) (τ : Equiv.Perm (Fin N)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), assignmentCost a τ ≤ assignmentCost a σ

/-- Talagrand (1995), p. 167: for `u > 0` the digraph
`D_u = { (i, j) ; X_{i,j} ≤ 2 u N⁻¹ log N }` of the cost matrix `X`. -/
noncomputable def digraphU (N : ℕ) (u : ℝ) (X : Fin N × Fin N → ℝ) : Set (Fin N × Fin N) :=
  {p | X p ≤ 2 * u * (N : ℝ)⁻¹ * Real.log N}

/-- Talagrand (1995), p. 166: the law of the cost matrix `(X_{i,j})_{i ∈ I, j ∈ J}` whose
`N²` entries are independent and uniformly distributed over `[0, 1]`: the product over
`Fin N × Fin N` of Lebesgue measure restricted to `[0, 1]`. A point of the sample space is
a cost matrix; its coordinates are the random variables `X_{i,j}`. -/
noncomputable def costLaw (N : ℕ) : Measure (Fin N × Fin N → ℝ) :=
  Measure.pi (fun _ : Fin N × Fin N => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))

end TalagrandConc.Assignment
