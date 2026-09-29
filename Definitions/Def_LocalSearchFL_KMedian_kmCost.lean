import Mathlib
import Definitions.Def_LocalSearchFL_Shared_MetricInstance

namespace LocalSearchFL.KMedian

/-- The **k-median cost** of a nonempty set `S` of open facilities (p. 548, §3):
`cost(S) = ∑_{j ∈ C} min_{i ∈ S} c_{ji}`, every client being served by its nearest open
facility. Only nonempty `S` have a cost. -/
noncomputable def kmCost {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  ∑ j : Cl, S.inf' hS (fun i => I.c j i)

/-- **Local optimality for single swaps** (p. 547 and §3.1, p. 548): `S` is locally optimum for
the neighbourhood `B(S) = {S − {s} + {s'} | s ∈ S}`, `s' ∉ S`, i.e. no single swap `⟨s, s'⟩`
closing `s ∈ S` and opening `s' ∉ S` decreases the cost. -/
def IsSwapLocalOpt {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : Prop :=
  ∀ s ∈ S, ∀ s' : Fa, s' ∉ S →
    kmCost I S hS ≤ kmCost I (insert s' (S.erase s)) (Finset.insert_nonempty s' (S.erase s))

/-- `σ` is a **nearest-facility assignment** for the solution `A` (p. 548): every client `j` is
assigned a facility `σ j ∈ A` at minimum distance from `j` among the facilities of `A`
(ties broken arbitrarily). Then `c_{j σ(j)}` is the service cost `A_j` of `j` in `A`. -/
def IsNearestAssignment {Cl Fa : Type} (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (A : Finset Fa)
    (σ : Cl → Fa) : Prop :=
  ∀ j, σ j ∈ A ∧ ∀ i ∈ A, I.c j (σ j) ≤ I.c j i

/-- The **neighbourhood** `N_A(a)` of a facility `a` under an assignment `σ` (p. 548): the set
of clients that `a` serves. -/
def nbhd {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (σ : Cl → Fa) (a : Fa) : Finset Cl :=
  Finset.univ.filter (fun j => σ j = a)

end LocalSearchFL.KMedian
