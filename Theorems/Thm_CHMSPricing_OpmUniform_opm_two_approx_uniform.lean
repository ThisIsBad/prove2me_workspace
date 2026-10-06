import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Mechanism
import Definitions.Def_CHMSPricing_OpmUniform_Opm

namespace CHMSPricing.OpmUniform

theorem opm_two_approx_uniform {n : ℕ} (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (k : ℕ) :
    ∃ p : Fin n → ℝ, ∀ M : Mechanism (Fin n), IsTruthful D (uniformSystem n k) M →
      revenue D M ≤ 2 * oblRevenue D (uniformSystem n k) p := by sorry

end CHMSPricing.OpmUniform

