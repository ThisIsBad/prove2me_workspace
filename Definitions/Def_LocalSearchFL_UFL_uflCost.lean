import Mathlib
import Definitions.Def_LocalSearchFL_UFL_MetricInstance

namespace LocalSearchFL.UFL

/-- The **facility cost** `cost_f(S) = ∑_{i ∈ S} f_i` of a set `S` of open facilities
(§4.2, p. 554). -/
def costF {Fa : Type} (f : Fa → ℝ) (S : Finset Fa) : ℝ :=
  ∑ i ∈ S, f i

/-- The **service cost** `cost_s(S) = ∑_{j ∈ C} min_{i ∈ S} c_{ji}` of a nonempty set `S` of open
facilities (§4.2, p. 554): every client is served by its nearest open facility. Only nonempty `S`
have a service cost. -/
noncomputable def costS {Cl Fa : Type} [Fintype Cl] (I : MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  ∑ j : Cl, S.inf' hS (fun i => I.c j i)

/-- The **UFL cost** `cost(S) = cost_f(S) + cost_s(S)` of a nonempty set `S` of open facilities
(§4, p. 554). -/
noncomputable def uflCost {Cl Fa : Type} [Fintype Cl] (I : MetricInstance Cl Fa) (f : Fa → ℝ)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  costF f S + costS I S hS

/-- **Local optimality for the add/drop/swap neighbourhood** (4) of §4.1, p. 554:
`B(S) = {S + {s'}} ∪ {S − {s} | s ∈ S} ∪ {S − {s} + {s'} | s ∈ S}`. The nonempty set `S` is
locally optimum if no neighbour has smaller cost: adding any facility `s'`, dropping any `s ∈ S`
(when a facility remains open), or swapping any `s ∈ S` for any facility `s'`. -/
def IsUFLLocalOpt {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (I : MetricInstance Cl Fa)
    (f : Fa → ℝ) (S : Finset Fa) (hS : S.Nonempty) : Prop :=
  (∀ s' : Fa, uflCost I f S hS ≤ uflCost I f (insert s' S) (Finset.insert_nonempty s' S)) ∧
  (∀ s ∈ S, ∀ h : (S.erase s).Nonempty, uflCost I f S hS ≤ uflCost I f (S.erase s) h) ∧
  (∀ s ∈ S, ∀ s' : Fa,
    uflCost I f S hS ≤ uflCost I f (insert s' (S.erase s)) (Finset.insert_nonempty s' (S.erase s)))

/-- `σ` is a **nearest-facility assignment** for the solution `A` (p. 548): every client `j` is
assigned a facility `σ j ∈ A` at minimum distance from `j` among the facilities of `A`
(ties broken arbitrarily). Then `c_{j σ(j)}` is the service cost `A_j` of `j` in `A`. -/
def IsNearestAssignment {Cl Fa : Type} (I : MetricInstance Cl Fa) (A : Finset Fa)
    (σ : Cl → Fa) : Prop :=
  ∀ j, σ j ∈ A ∧ ∀ i ∈ A, I.c j (σ j) ≤ I.c j i

/-- The **neighbourhood** `N_A(a)` of a facility `a` under an assignment `σ` (p. 548): the set
of clients that `a` serves. -/
def nbhd {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (σ : Cl → Fa) (a : Fa) : Finset Cl :=
  Finset.univ.filter (fun j => σ j = a)

end LocalSearchFL.UFL
