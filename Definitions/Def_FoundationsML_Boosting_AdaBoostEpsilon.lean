import Mathlib
import Definitions.Def_FoundationsML_Boosting_WeightedError
import Definitions.Def_FoundationsML_Boosting_AdaBoostDist

namespace FoundationsML.Boosting

/-- AdaBoost's own round-`t` weighted error `ε_t`, the error of the `t`-th selected base
classifier `h t` under AdaBoost's own distribution `D_t` at that round (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Figure 7.1 line 4, p.
146, PDF p. 163): `ε_t = P_{i∼D_t}[h_t(x_i) ≠ y_i]`. -/
noncomputable def AdaBoostEpsilon {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (t : ℕ) : ℝ :=
  WeightedError (AdaBoostDist S y h t) S y (h t)

end FoundationsML.Boosting
