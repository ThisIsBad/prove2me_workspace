import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

/-- Kingman, §1.4, (1.4.1), p. 887. The infimum formula and the real-time limit
are stated under (1.4.7). Formalization Note: S₁–S₃ alone do not imply this
continuous-time limit: a discontinuous additive Hamel function gives a
deterministic counterexample. The local oscillation condition rules it out;
(1.4.7) carries its own a.e. measurability, so separability is not assumed. -/
theorem gamma_limit {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    BddBelow (Set.range (fun t : {t : ℝ // 0 < t} => mean P x t / (t : ℝ))) ∧
      Tendsto (fun t : ℝ => mean P x t / t) atTop (𝓝 (gamma P x)) := by sorry

end KingmanSubadditive.Continuous

