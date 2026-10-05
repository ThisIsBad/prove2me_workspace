import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

namespace PriceOfStability.WeightedSingle

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*,
SIAM J. Comput. 38 (2008), Theorem 6.3, p. 1620 (PDF p. 19): "For any weighted game in which all
players have the same source s and sink t, best response dynamics converge to a Nash
equilibrium, and hence Nash equilibria exist."

Let `D` be a finite directed multigraph with source `s` and sink `t`, let every player's strategy
family be the set of simple `s`–`t` paths, and let the weights satisfy `wᵢ ≥ 1` and the arc costs
`c_e ≥ 0`. Then
1. there is no infinite sequence of best-response moves (the relation "`S'` is reached from `S`
   by one best-response move" is well-founded with `S'` below `S`);
2. a profile from which no best-response move is possible is a Nash equilibrium;
3. if an `s`–`t` path exists, a Nash equilibrium exists.

**Formalization Note.** `WellFounded r` with `r S' S :↔ IsBRMove Γ S S'` says every descending
`r`-chain, i.e. every run of best-response dynamics, is finite. Costs are only assumed
nonnegative, as in Sect. 2 (the proof's milestones assume positive costs). -/
theorem theorem6_3 {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard) :
    WellFounded (fun S' S => IsBRMove (singleCommodityGame D s t w c) S S') ∧
    (∀ S, IsProfile (singleCommodityGame D s t w c) S →
      (¬ ∃ S', IsBRMove (singleCommodityGame D s t w c) S S') →
      IsNash (singleCommodityGame D s t w c) S) ∧
    ((stPaths D s t).Nonempty → ∃ S, IsNash (singleCommodityGame D s t w c) S) := by sorry

end PriceOfStability.WeightedSingle

