import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- An undirected capacitated network. A pair is an edge precisely when its capacity is
strictly positive. Parallel edges are represented by their summed capacity. -/
structure Network (V : Type) where
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_symm : ∀ u v, C u v = C v u
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The capacity of the edges crossing a cut, each undirected edge counted once. -/
noncomputable def cutCap (N : Network V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- The standing connectedness convention of p. 789. -/
def IsConnectedNet (N : Network V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < cutCap N U

/-- The graph supported by positive-capacity pairs. -/
noncomputable def Network.graph (N : Network V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => 0 < N.C u v)

/-- The ratio cost of a cut. Used only for nonempty proper cuts, so the denominator is
positive. -/
noncomputable def ratioCost (N : Network V) (U : Finset V) : ℝ :=
  cutCap N U / ((U.card : ℝ) * (Uᶜ.card : ℝ))

/-- The uniform sparsest cut. With at least two vertices, the index of proper cuts is
nonempty and finite; improper cuts would give a spurious `0 / 0` in Lean. -/
noncomputable def minCut (N : Network V) : ℝ :=
  ⨅ U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty}, ratioCost N U.1

end LeightonRao.Uniform
