import Definitions.Def_ComplexScheduling_RCPSP
import Definitions.Def_ComplexScheduling_JobShop
import Definitions.Def_ComplexScheduling_ConstraintPropagation

namespace ComplexScheduling
theorem input_test {n r : ℕ} (p : Fin n → ℕ) (Rcap : Fin r → ℕ)
    (demand : Fin n → Fin r → ℕ) (prec C D : Finset (Fin n × Fin n)) (rel dl : Fin n → ℕ)
    (I : Finset (Fin n)) (hI : IsDisjunctiveSet C D I) (hp : ∀ i ∈ I, 0 < p i)
    (Ω : Finset (Fin n)) (hΩ : Ω ⊆ I) (hne : Ω.Nonempty) (i : Fin n) (hi : i ∈ I) (hiΩ : i ∉ Ω)
    (hcond : ∀ μ ∈ insert i Ω, ∀ ν ∈ Ω, dl μ < rel ν + totalProcessing p (insert i Ω))
    (S : Fin n → ℕ) (hS : FeasibleSchedule p Rcap demand prec S) (hC : RespectsArcs p C S)
    (hD : SatisfiesDisjunctions p D S) (hw : WithinWindows rel dl p S) :
    ∀ j ∈ Ω, S i + p i ≤ S j := by sorry
end ComplexScheduling
