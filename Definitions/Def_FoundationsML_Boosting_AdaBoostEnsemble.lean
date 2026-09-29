import Mathlib
import Definitions.Def_FoundationsML_Boosting_AdaBoostAlpha
import Definitions.Def_FoundationsML_Boosting_AdaBoostEpsilon

namespace FoundationsML.Boosting

/-- The function `f = ∑_{t=1}^T α_t h_t` returned by AdaBoost after `T` rounds of boosting
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Figure 7.1 lines 9-10, p. 146, PDF p. 163), with `α_t = AdaBoostAlpha ε_t` and `ε_t` AdaBoost's
own round-`t` weighted error (`AdaBoostEpsilon`). -/
noncomputable def AdaBoostEnsemble {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) (T : ℕ) : X → ℝ :=
  fun x => ∑ t ∈ Finset.range T, AdaBoostAlpha (AdaBoostEpsilon S y h t) * h t x

end FoundationsML.Boosting
