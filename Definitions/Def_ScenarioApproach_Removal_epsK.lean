import Mathlib

namespace ScenarioApproach.Removal

/-- The violation level `ε_k` of formula (1.9) (Campi–Garatti 2018, p. 18):
`ε_k = k/N + [√k/N + ((√k+1)/N)((d−1) ln(k+d−1) + (d−1)/√k + ln(1/β))]`. -/
noncomputable def epsK (N k d : ℕ) (β : ℝ) : ℝ :=
  (k : ℝ) / N + (Real.sqrt k / N + (Real.sqrt k + 1) / N *
    (((d : ℝ) - 1) * Real.log ((k : ℝ) + d - 1) + ((d : ℝ) - 1) / Real.sqrt k + Real.log (1 / β)))

end ScenarioApproach.Removal
