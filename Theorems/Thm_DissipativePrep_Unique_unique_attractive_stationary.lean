import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16

namespace DissipativePrep.Unique

theorem unique_attractive_stationary {n : ℕ} (hn : 1 ≤ n)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) (gmin : ℝ) (hgmin : IsLeast (Set.range g) gmin) :
    (∀ (H : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hH : H.IsHermitian) (E : ℝ),
        act H (target U) = (E : ℂ) • target U →
        ∀ ρ, stationary (prepData U g H hH) ρ ↔ ρ = pureDensity (target U)) ∧
    attractive (prepData U g 0 Matrix.isHermitian_zero) (pureDensity (target U)) ∧
    IsLeast (relaxRates (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero))) gmin ∧
    IsRelaxTime (gkslGenerator (prepData U g 0 Matrix.isHermitian_zero)) (1 / gmin) := by sorry

end DissipativePrep.Unique

