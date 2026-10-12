import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory

namespace NagaevLD.GenMoment

/-- Convexity step of the proof of Theorem 2.5, p. 767: `g′(x/n)·x/n ≥ g(x/n) − g(0)` and,
for `h = g′(x/n)`, `e^{hx/n − g(x/n)} ≥ e^{−g(0)}`. (The page prints a strict `>` in the first
inequality; it fails when `g′` is constant on `[0, x/n]`, so the non-strict form is stated.) -/
theorem convexity_step (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    g (x / n) - g 0 ≤ g' (x / n) * (x / n) ∧
      Real.exp (-g 0) ≤ Real.exp (h * (x / n) - g (x / n)) := by sorry

end NagaevLD.GenMoment

