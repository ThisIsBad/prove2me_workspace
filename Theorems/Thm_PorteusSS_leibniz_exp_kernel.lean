import Mathlib

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 5 (p. 422). If `g` is continuous on `ℝ`, `lam > 0`, and
`f(x) = ∫_0^∞ g(x - t) lam e^{-lam t} dt` exists (is finite) for every `x`, then `f` is
continuously differentiable on `ℝ` and `f'(x) = lam (g(x) - f(x))`  (23). -/
theorem leibniz_exp_kernel (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hg : Continuous g)
    (hint : ∀ x : ℝ,
      IntegrableOn (fun t => g (x - t) * (lam * Real.exp (-lam * t))) (Ici 0)) :
    ContDiff ℝ 1 (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t))) ∧
      ∀ x : ℝ, HasDerivAt (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))
        (lam * (g x - ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))) x := by sorry

end PorteusSS
