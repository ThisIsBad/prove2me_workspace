import Mathlib
import Definitions.Def_LocalSearchFL_Shared_MetricInstance

namespace LocalSearchFL.MultiSwap

/-- The **k-median cost** of a nonempty set `S` of open facilities (p. 548, §3):
`cost(S) = ∑_{j ∈ C} min_{i ∈ S} c_{ji}`, every client being served by its nearest open
facility. Only nonempty `S` have a cost. -/
noncomputable def kmCost {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  ∑ j : Cl, S.inf' hS (fun i => I.c j i)

/-- **Local optimality for p-swaps** (p. 547 and §3.3, eq. (3), p. 551): `S` is locally optimum
for the neighbourhood `B(S) = {(S \ A) ∪ B | A ⊆ S, B ⊆ F, |A| = |B| ≤ p}`, i.e. no swap `⟨A, B⟩`
deleting a set `A ⊆ S` of at most `p` facilities and adding a set `B` of `|A|` facilities
decreases the cost. (`B` may meet `S`.) Whenever `S` is nonempty every such neighbour is
nonempty, so the quantifier over its nonemptiness proof `h` restricts nothing. -/
def IsPSwapLocalOpt {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (p : ℕ) (S : Finset Fa) (hS : S.Nonempty) : Prop :=
  ∀ A : Finset Fa, A ⊆ S → ∀ B : Finset Fa, A.card = B.card → A.card ≤ p →
    ∀ h : ((S \ A) ∪ B).Nonempty, kmCost I S hS ≤ kmCost I ((S \ A) ∪ B) h

end LocalSearchFL.MultiSwap
