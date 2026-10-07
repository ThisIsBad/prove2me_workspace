import Mathlib
noncomputable section

namespace WardropTraffic.MeanSpeed

/-- Concentration of subsidiary stream i, equation (1). -/
def conc {C : ℕ} (q v : Fin C → ℝ) (i : Fin C) : ℝ := q i / v i

/-- Total flow Q. -/
def totalFlow {C : ℕ} (q : Fin C → ℝ) : ℝ := ∑ i, q i

/-- Total concentration K. -/
def totalConc {C : ℕ} (q v : Fin C → ℝ) : ℝ := ∑ i, conc q v i

/-- Frequency of stream i among vehicles passing a point. -/
def timeFreq {C : ℕ} (q : Fin C → ℝ) (i : Fin C) : ℝ := q i / totalFlow q

/-- Frequency of stream i among vehicles occupying road space. -/
def spaceFreq {C : ℕ} (q v : Fin C → ℝ) (i : Fin C) : ℝ :=
  conc q v i / totalConc q v

/-- Time-mean speed, equation (2). -/
def timeMean {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  (∑ i, q i * v i) / totalFlow q

/-- Space-mean speed, equation (3). -/
def spaceMean {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  (∑ i, conc q v i * v i) / totalConc q v

/-- Variance of the space distribution, equation (7). -/
def spaceVar {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  (∑ i, conc q v i * (v i - spaceMean q v) ^ 2) / totalConc q v

/-- Standard deviation of the space distribution. -/
def spaceSD {C : ℕ} (q v : Fin C → ℝ) : ℝ := Real.sqrt (spaceVar q v)

/-- Coefficient of variation of the space distribution. -/
def spaceCV {C : ℕ} (q v : Fin C → ℝ) : ℝ := spaceSD q v / spaceMean q v

/-- Number of overtakings per unit road length and time, in the ordered-speed model. -/
def overtakingRate {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then conc q v i * conc q v j * (v j - v i) else 0

end WardropTraffic.MeanSpeed
