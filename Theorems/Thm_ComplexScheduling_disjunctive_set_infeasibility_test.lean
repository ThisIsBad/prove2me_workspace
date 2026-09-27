import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem disjunctive_set_infeasibility_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I)
    (J : Finset (Fin n)) (hJI : J ⊆ I) (hJ : J.Nonempty)
    (hcond : ∀ μ ∈ J, ∀ ν ∈ J, dl μ < rel ν + totalProcessing p J) :
    ¬ ∃ S : Fin n → ℕ, FeasibleSchedule p Rcap demand prec S ∧ RespectsArcs p C S ∧
      SatisfiesDisjunctions p D S ∧ WithinWindows rel dl p S := by sorry
end ComplexScheduling
