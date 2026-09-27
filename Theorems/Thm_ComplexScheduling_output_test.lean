import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem output_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I) (hp : ∀ i ∈ I, 0 < p i)
    (Ω : Finset (Fin n)) (hΩ : Ω ⊆ I) (hne : Ω.Nonempty) (i : Fin n) (hi : i ∈ I) (hiΩ : i ∉ Ω)
    (hcond : ∀ μ ∈ Ω, ∀ ν ∈ insert i Ω, dl μ < rel ν + totalProcessing p (insert i Ω))
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    ∀ j ∈ Ω, S j + p j ≤ S i := by sorry
end ComplexScheduling
