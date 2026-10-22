import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.TwoGap

theorem lemma_3 (m : ℕ) (hm_even : Even m) (hm0 : 0 < m) :
    ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ),
      AffinePolicies.Simplex.IsOptimalAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) x P q ∧ ∀ i j, q i = q j := by sorry

end AffinePolicies.TwoGap

