import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3.2, pp. 69–70 (goal): the minimizer of `h(x) = (ρ/2)‖Aᵢx − v‖₂² + λ‖x‖₂` is `0` iff
`‖Aᵢᵀv‖₂ ≤ λ/ρ`; otherwise it is `(AᵢᵀAᵢ + νI)⁻¹Aᵢᵀv` for the value `ν > 0` with
`ν‖xᵢ‖₂ = λ/ρ`. -/
theorem group_lasso_block_update {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    (IsMinOn (groupLassoObj ρ lam A v) Set.univ 0 ↔
        ‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ) ∧
    (‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ →
        ∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x → x = 0) ∧
    (lam / ρ < ‖Matrix.toEuclideanLin Aᵀ v‖ →
        (∃! ν : ℝ, 0 < ν ∧ ν * ‖ridgeSol A ν v‖ = lam / ρ) ∧
        (∀ ν : ℝ, 0 < ν → ν * ‖ridgeSol A ν v‖ = lam / ρ →
          IsMinOn (groupLassoObj ρ lam A v) Set.univ (ridgeSol A ν v)) ∧
        (∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x →
          ∃ ν : ℝ, 0 < ν ∧ ν * ‖x‖ = lam / ρ ∧ x = ridgeSol A ν v)) := by sorry

end BoydADMM.ModelFit

