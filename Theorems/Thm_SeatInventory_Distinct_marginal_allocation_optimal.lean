import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel
import Definitions.Def_SeatInventory_Distinct_MarginalAllocation

namespace SeatInventory.Distinct

/-- Belobaba 1987, Sect. 4.2, p. 90: since `m_i(k)` decreases in `k`, the `n` largest values
`m_i(k)` across all fare classes determine the revenue-maximising booking limits. For every set
`T` of `n` largest values of `m_i(k) = f_i · P[r_i ≥ k]` over (class, seat) pairs with
`1 ≤ k ≤ n`, the allocation `S^T_i = #{k : (i, k) ∈ T}` uses exactly `n` seats and its total
expected revenue `Σ_i f_i · E[min(r_i, S_i)]` is at least that of every allocation `S` of at
most `n` seats to distinct fare-class inventories. Fares are nonnegative. -/
theorem marginal_allocation_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (d : ι → PMF ℕ) (n : ℕ) (T : Finset (ι × ℕ))
    (hT : IsTopN (marginalRevenue f d) (seatPairs ι n) T n) :
    ∑ i, allocationOf T i = n ∧
    ∀ S : ι → ℕ, ∑ i, S i ≤ n →
      totalExpectedRevenue f d S ≤ totalExpectedRevenue f d (allocationOf T) := by sorry

end SeatInventory.Distinct

