import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 6 (p. 422). If `g` is piecewise continuous and PF-integrable on `ℝ` and `φ` is a
one-sided Pólya density, then `g * φ` is continuous on `ℝ` and continuously differentiable
outside a finite set; and if `φ` is the exponential density with parameter `lam > 0`, then
`(g * φ)'(x) = lam (g(x) - (g * φ)(x))` at every point `x` where `g` is continuous. -/
theorem conv_polya_smooth (g φ : ℝ → ℝ) (hg_pc : PiecewiseContinuousOn g univ)
    (hg_pf : PFIntegrable g) (hφ : IsOneSidedPolyaDensity φ) :
    Continuous (conv g φ) ∧
      (∃ A : Finset ℝ, ∀ x : ℝ, x ∉ A → ContDiffAt ℝ 1 (conv g φ) x) ∧
      (∀ lam : ℝ, 0 < lam → φ = expDensity lam → ∀ x : ℝ, ContinuousAt g x →
        HasDerivAt (conv g φ) (lam * (g x - conv g φ x)) x) := by sorry

end PorteusSS
