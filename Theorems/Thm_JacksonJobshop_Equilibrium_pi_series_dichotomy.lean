import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

/-- Jackson (1963), p. 136, sentence after (4.4): the series `Σ_K W(K) T(K)` in (4.4) either
converges to a positive number or diverges to `+∞`. -/
theorem pi_series_dichotomy {N : ℕ} (sys : JobshopSystem N) :
    (Summable (fun K => W sys K * T sys K) → 0 < ∑' K, W sys K * T sys K) ∧
    (¬ Summable (fun K => W sys K * T sys K) →
      Filter.Tendsto (fun M => ∑ K ∈ Finset.range M, W sys K * T sys K)
        Filter.atTop Filter.atTop) := by sorry

end JacksonJobshop.Equilibrium
