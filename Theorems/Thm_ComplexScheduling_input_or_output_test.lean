import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem input_or_output_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I) (hp : ∀ i ∈ I, 0 < p i)
    (J : Finset (Fin n)) (hJI : J ⊆ I) (hJ : 2 ≤ J.card) (i j : Fin n) (hi : i ∈ J) (hj : j ∈ J)
    (hcond : ∀ μ ∈ J.erase j, ∀ ν ∈ J.erase i, dl μ < rel ν + totalProcessing p J)
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    (StartsFirstIn S J i ∨ EndsLastIn p S J j) ∧ (i ≠ j → S i + p i ≤ S j) := by sorry
end ComplexScheduling
