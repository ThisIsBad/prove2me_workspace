import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eq. (5.13), p. 107 (with (5.12), p. 105, and (4.3)–(4.4), p. 86), discrete
reading: an allocation `S` of exactly `C` seats to distinct fare-class inventories maximises total
expected revenue among all allocations of `C` seats iff there is a `λ` lying between the EMSR
of the last seat allocated to each class and the EMSR of the next seat of each class:
`EMSR_i(S_i) ≥ λ` whenever `S_i ≥ 1`, and `EMSR_i(S_i + 1) ≤ λ`, for every class `i`.
Fares are nonnegative. -/
theorem emsr_optimality_conditions {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (d : ι → PMF ℕ) (C : ℕ) (S : ι → ℕ) (hS : ∑ i, S i = C) :
    (∀ S' : ι → ℕ, ∑ i, S' i = C → totalExpectedRevenue f d S' ≤ totalExpectedRevenue f d S) ↔
      ∃ lam : ℝ, ∀ i, (1 ≤ S i → lam ≤ emsr (f i) (d i) (S i)) ∧
        emsr (f i) (d i) (S i + 1) ≤ lam := by sorry

end SeatInventory.Distinct

