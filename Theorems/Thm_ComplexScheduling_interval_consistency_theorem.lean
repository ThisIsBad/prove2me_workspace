import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem interval_consistency_theorem {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I)
    (J J' J'' : Finset (Fin n)) (hJI : J ⊆ I) (hJ' : J' ⊂ J) (hJ'' : J'' ⊂ J)
    (hne : (J' ∪ J'').Nonempty)
    (hcond : ∀ ν ∈ J \ J', ∀ μ ∈ J \ J'', ν ≠ μ → dl μ < rel ν + totalProcessing p J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    (∃ i ∈ J', StartsFirstIn S J i) ∨ ∃ i ∈ J'', EndsLastIn p S J i := by sorry
end ComplexScheduling
