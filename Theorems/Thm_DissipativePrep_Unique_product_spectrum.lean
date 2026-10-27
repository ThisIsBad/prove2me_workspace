import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem product_spectrum {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    let G := gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)
    let σ := fun i : Fin n → Fin 4 => U * tensorEigenoperator i * Uᴴ
    (∀ i, G (σ i) = (∑ k, localEigenvalue (g k) (i k)) • σ i) ∧
    LinearIndependent ℂ σ ∧
    Submodule.span ℂ (Set.range σ) = ⊤ ∧
    (∀ μ : ℂ, G.HasEigenvalue μ ↔
      ∃ m : Fin n → Fin 3, μ = -(∑ k, ((m k : ℕ) : ℂ) * (g k : ℂ))) := by sorry

end DissipativePrep.Unique

