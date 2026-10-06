import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Mechanism

namespace CHMSPricing.OpmUniform

open MeasureTheory

theorem revenue_eq_virtual_surplus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (J : SetSystem ι) (M : Mechanism ι)
    (hM : IsTruthful D J M)
    (hnorm : ∀ v ∈ typeSpace D, ∀ i,
      M.utility i (D i).lo (Function.update v i (D i).lo) = 0) :
    revenue D M = ∫ v, virtualSurplus D (M.alloc v) v ∂(prior D) := by sorry

end CHMSPricing.OpmUniform

