import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue
import Definitions.Def_OnlinePrimalDual_AdAuctions_actualCharge
import Definitions.Def_OnlinePrimalDual_AdAuctions_allocRun_v2


namespace OnlinePrimalDual.AdAuctions

/-- **Theorem 10.1** (Buchbinder & Naor, FnT TCS 2009, p. 212-215) — the Allocation algorithm is
`(1 − 1/c)(1 − Rmax)`-competitive, with `c = (1 + Rmax)^{1/Rmax}`; the goal of this mission.
The run is the algorithm's own: items arrive in the order `ord` (a permutation of `M`), item `j`
is allocated to `alloc j`, which `halloc` requires to be a buyer maximizing `b(i,j)(1 − x(i))`
over all buyers at the moment `j` arrives (`x` being the primal values after the items before
`j` — `ord.takeWhile (· ≠ j)` — have been processed; ties are arbitrary, as in the book), and
`allocRun inst ord alloc` lists the bids each buyer was actually charged for (step (2), "if
`x(i) ≥ 1` do nothing", and step (3)'s update of `x(i)`, both built into `allocRun`). The retired
version let the charged-bid lists be a free variable constrained only by two consequences of the
run ((10.1) and Claim (3)), which the empty run satisfies. The conclusion is the book's statement
via weak duality: the revenue actually collected, `∑ᵢ min(∑ charged bids, B(i))`, is at least
`(1 − 1/c)(1 − Rmax)` times the objective of every feasible solution `y''` of the packing
(maximization) LP of Fig. 10.1, hence at least that fraction of the offline optimum. -/
theorem allocation_competitive_ratio_v2 {I M : Type*} [Fintype I] [Fintype M] [DecidableEq I]
    [DecidableEq M] (inst : AdAuctionsInstance I M) (ord : List M) (hord_nodup : ord.Nodup)
    (hord_mem : ∀ j, j ∈ ord) (alloc : M → I)
    (halloc : ∀ j i,
      inst.b i j * (1 - buyerX inst i (allocRun inst (ord.takeWhile (· ≠ j)) alloc i)) ≤
        inst.b (alloc j) j *
          (1 - buyerX inst (alloc j) (allocRun inst (ord.takeWhile (· ≠ j)) alloc (alloc j)))) :
    ∀ y'' : I → M → ℝ, (∀ i j, 0 ≤ y'' i j) →
      (∀ j, ∑ i, y'' i j ≤ 1) →
      (∀ i, ∑ j, inst.b i j * y'' i j ≤ inst.B i) →
      ∑ i, actualCharge inst (allocRun inst ord alloc) i ≥
        (1 - 1 / cParam inst) * (1 - inst.Rmax) *
          (∑ i, ∑ j, inst.b i j * y'' i j) := by sorry

end OnlinePrimalDual.AdAuctions

