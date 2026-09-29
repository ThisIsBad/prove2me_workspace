import Mathlib

namespace GallegoOzerADI.PositiveSetup

/-- The myopic order-up-to level of the stationary problem (p. 1350):
`S^m = min {y : G(y) ≤ G(x) for all x}`, the least global minimizer of the single-period cost
`G`. -/
noncomputable def myopicOrderUpTo (G : ℝ → ℝ) : ℝ :=
  sInf {y : ℝ | ∀ x, G y ≤ G x}

/-- The myopic reorder point of the stationary problem (p. 1350):
`s^m = max {y ≤ S^m : G(y) ≥ K + G(S^m)}`. -/
noncomputable def myopicReorderPoint (G : ℝ → ℝ) (K : ℝ) : ℝ :=
  sSup {y : ℝ | y ≤ myopicOrderUpTo G ∧ K + G (myopicOrderUpTo G) ≤ G y}

/-- The upper bound `S̄` of p. 1350, printed as `min {y > S^m : G(y) > G(S^m) + α K}`. That set
is open for continuous `G` and has no minimum, so it is read as the infimum. -/
noncomputable def myopicUpperLevel (G : ℝ → ℝ) (K α : ℝ) : ℝ :=
  sInf {y : ℝ | myopicOrderUpTo G < y ∧ G (myopicOrderUpTo G) + α * K < G y}

end GallegoOzerADI.PositiveSetup
