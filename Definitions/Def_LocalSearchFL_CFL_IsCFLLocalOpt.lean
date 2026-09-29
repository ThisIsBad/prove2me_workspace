import Mathlib
import Definitions.Def_LocalSearchFL_CFL_CFLSol

namespace LocalSearchFL.CFL

variable {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}

/-- `Y` is an **add neighbour** of `X` (first part of (9), §5.1 p. 558): the multiset of
facilities of `Y` is that of `X` plus a single new copy of some facility `s'`, i.e.
`Y = S + s'`. The assignment of `Y` is any capacity-feasible one. -/
def IsAddNbr (X Y : CFLSol Cl Fa u) : Prop :=
  ∃ s' : Fa, Y.facMultiset = X.facMultiset + {s'}

/-- `Y` is a **drop-add neighbour** of `X` (second part of (9), §5.1 p. 558): for some set
`T` of copies of `X`, some facility `s'` and some `l ≥ 1` with `l · u_{s'} ≥ |N_X(T)|`, the
multiset of facilities of `Y` is `S − T + l · {s'}`: the copies of `X` outside `T`, plus `l`
new copies of `s'`. The assignment of `Y` is any capacity-feasible one. -/
def IsDropAddNbr (X Y : CFLSol Cl Fa u) : Prop :=
  ∃ (T : Finset (Fin X.n)) (s' : Fa) (l : ℕ), 1 ≤ l ∧ (X.nbhdSet T).card ≤ l * u s' ∧
    Y.facMultiset = Multiset.map X.loc (Finset.univ \ T).val + Multiset.replicate l s'

/-- **Local optimality for the neighbourhood (9)** of §5.1, p. 558:
`B(S) = {S + s' | s' ∈ F} ∪ {S − T + l·{s'} | s' ∈ F, T ⊆ S, l·u_{s'} ≥ |N_S(T)|}`.
`X` is locally optimum if `cost X ≤ cost Y` for every solution `Y` (with any feasible
assignment) whose multiset of facilities is a neighbour of that of `X`. -/
def IsCFLLocalOpt (I : MetricInstance Cl Fa) (f : Fa → ℝ) (X : CFLSol Cl Fa u) : Prop :=
  ∀ Y : CFLSol Cl Fa u, (IsAddNbr X Y ∨ IsDropAddNbr X Y) → cost I f X ≤ cost I f Y

end LocalSearchFL.CFL
