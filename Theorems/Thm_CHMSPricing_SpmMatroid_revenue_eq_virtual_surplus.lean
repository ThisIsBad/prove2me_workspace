import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism

namespace CHMSPricing.SpmMatroid

open MeasureTheory

/-- Proposition 1 (p. 5): with regular value distributions, the expected revenue of a truthful
mechanism equals its expected virtual surplus `𝔼_v[Φ(M(v), v)]`, under the normalization that
an agent with the lowest value `loᵢ` gets zero utility (p. 12: payments "uniquely determined
by the allocation rule assuming that agents that are not served pay nothing"). -/
theorem revenue_eq_virtual_surplus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (hnorm : ∀ v ∈ typeSpace D, ∀ i,
      M.utility i (D i).lo (Function.update v i (D i).lo) = 0) :
    revenue D M = ∫ v, virtualSurplus D (M.alloc v) v ∂(prior D) := by sorry

end CHMSPricing.SpmMatroid

