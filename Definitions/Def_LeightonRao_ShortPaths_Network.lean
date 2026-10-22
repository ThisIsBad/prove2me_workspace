import Mathlib

namespace LeightonRao.ShortPaths

/-- A finite undirected capacitated network. A pair is an edge exactly when its capacity is positive. -/
structure Network (V : Type) where
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_symm : ∀ u v, C u v = C v u
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

def Network.graph (N : Network V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => 0 < N.C u v)

def cutCap (N : Network V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- The paper's standing connectivity assumption, stated in cut form. -/
def IsConnectedNet (N : Network V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < cutCap N U

noncomputable def ratioCost (N : Network V) (U : Finset V) : ℝ :=
  cutCap N U / ((U.card : ℝ) * (Uᶜ.card : ℝ))

/-- The infimum is over nonempty proper cuts. It is a genuine minimum when `2 ≤ card V`. -/
noncomputable def minCut (N : Network V) : ℝ :=
  ⨅ U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty}, ratioCost N U.1

noncomputable def uniformDemand (s t : V) : ℝ := if s = t then 0 else 1 / 2

end LeightonRao.ShortPaths
