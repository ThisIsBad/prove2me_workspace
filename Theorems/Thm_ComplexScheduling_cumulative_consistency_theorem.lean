import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem cumulative_consistency_theorem {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (k : Fin r) (J J' J'' : Finset (Fin n)) (hJk : ∀ i ∈ J, 0 < demand i k)
    (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'',
      Rcap k * dl μ < Rcap k * rel ν + totalWork p demand k J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by sorry
end ComplexScheduling
