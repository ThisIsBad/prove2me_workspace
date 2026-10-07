import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network

namespace CostScaling.Refine

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Network (V : Type*) [Fintype V] [DecidableEq V] :=
  CycleCanceling.MinMean.CircNetwork V

/-- Equations (2) and (3), on the arcs of the circulation network. -/
def IsPseudoflow (N : Network V) (f : V → V → ℝ) : Prop :=
  (∀ v w, (v, w) ∈ N.E → f v w ≤ N.u v w) ∧
  (∀ v w, (v, w) ∈ N.E → f v w = -f w v)

/-- Excess is incoming flow, with the outgoing-neighbour filter justified by symmetry. -/
def excess (N : Network V) (f : V → V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ Finset.univ.filter (fun w => (v, w) ∈ N.E), f w v

def IsActive (N : Network V) (f : V → V → ℝ) (v : V) : Prop :=
  0 < excess N f v

def IsResidualArc (N : Network V) (f : V → V → ℝ) (v w : V) : Prop :=
  (v, w) ∈ N.E ∧ 0 < CycleCanceling.MinMean.resCap N f v w

/-- The sign convention of this paper is `c(v,w) - p(v) + p(w)`. -/
def reducedCost (N : Network V) (p : V → ℝ) (v w : V) : ℝ :=
  N.c v w - p v + p w

/-- Equation (7), in its residual-arc form on p. 7. -/
def IsEpsOptimal (N : Network V) (ε : ℝ) (f : V → V → ℝ) (p : V → ℝ) : Prop :=
  IsPseudoflow N f ∧
  ∀ v w, IsResidualArc N f v w → -ε ≤ reducedCost N p v w

def IsAdmissible (N : Network V) (f : V → V → ℝ) (p : V → ℝ) (v w : V) : Prop :=
  IsResidualArc N f v w ∧ reducedCost N p v w < 0

/-- The paper's pseudoflow and vertex prices at one point of the loop. -/
structure State (V : Type*) where
  f : V → V → ℝ
  p : V → ℝ

/-- Figure 4 saturation, setting both antisymmetric directions of an edge. -/
noncomputable def initialFlow (N : Network V) (f₀ : V → V → ℝ) (p₀ : V → ℝ) (v w : V) : ℝ :=
  if (v, w) ∈ N.E ∧ reducedCost N p₀ v w < 0 then N.u v w
  else if (v, w) ∈ N.E ∧ reducedCost N p₀ w v < 0 then -N.u w v
  else f₀ v w

noncomputable def initialState (N : Network V) (f₀ : V → V → ℝ) (p₀ : V → ℝ) : State V :=
  ⟨initialFlow N f₀ p₀, p₀⟩

end CostScaling.Refine
