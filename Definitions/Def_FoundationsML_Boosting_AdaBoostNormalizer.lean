import Mathlib

namespace FoundationsML.Boosting

/-- AdaBoost's per-round normalization factor `Z_t`, as a function of the base classifier's
weighted error `ε` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, Figure 7.1 line 6, p. 146, PDF p. 163): `Z(ε) = 2·sqrt(ε(1−ε))`. -/
noncomputable def AdaBoostNormalizer (ε : ℝ) : ℝ := 2 * Real.sqrt (ε * (1 - ε))

end FoundationsML.Boosting
