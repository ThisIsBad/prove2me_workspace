import Mathlib
import Definitions.Def_FoundationsML_Boosting_WeightedError
import Definitions.Def_FoundationsML_Boosting_AdaBoostAlpha
import Definitions.Def_FoundationsML_Boosting_AdaBoostNormalizer

namespace FoundationsML.Boosting

/-- AdaBoost's sample-weight distribution `D_t` at the start of round `t` (`t = 0` is the
initial uniform distribution `D_1` of Figure 7.1 lines 1-2; `t + 1` is `D_{t+2}`, obtained from
`D_{t+1}` by the update of Figure 7.1 line 8, using the `t`-th selected base classifier `h t`)
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
Figure 7.1, p. 146, PDF p. 163). -/
noncomputable def AdaBoostDist {X : Type*} {m : ℕ}
    (S : Fin m → X) (y : Fin m → ℝ) (h : ℕ → X → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ => 1 / (m : ℝ)
  | t + 1 => fun i =>
      let D := AdaBoostDist S y h t
      let ε := WeightedError D S y (h t)
      let α := AdaBoostAlpha ε
      D i * Real.exp (-α * y i * h t (S i)) / AdaBoostNormalizer ε

end FoundationsML.Boosting
