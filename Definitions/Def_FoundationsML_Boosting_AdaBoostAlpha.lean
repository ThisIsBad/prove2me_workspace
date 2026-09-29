import Mathlib

namespace FoundationsML.Boosting

/-- AdaBoost's per-round coefficient `α_t`, as a function of the base classifier's weighted
error `ε` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT
Press 2018, Figure 7.1 line 5, p. 146, PDF p. 163): `α(ε) = (1/2)·log((1−ε)/ε)`. -/
noncomputable def AdaBoostAlpha (ε : ℝ) : ℝ := (1 / 2) * Real.log ((1 - ε) / ε)

end FoundationsML.Boosting
