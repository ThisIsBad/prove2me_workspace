import Mathlib
import Definitions.Def_FoundationsML_MultiClass_MarginFunction
import Definitions.Def_FoundationsML_MultiClass_MarginLossFunction

namespace FoundationsML.MultiClass

/-- The empirical margin loss of a multi-class scoring function `h : X × Y → ℝ` on a sample
`S : Fin m → X` against a target labeling function `f : X → Y` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (9.5), p. 215, PDF
p. 232): `R̂_{S,ρ}(h) = (1/m) ∑_{i=1}^m Φ_ρ(ρ_h(x_i,y_i))`. -/
noncomputable def EmpiricalMarginLoss {X Y : Type*} {m : ℕ}
    (ρ : ℝ) (S : Fin m → X) (f : X → Y) (h : X × Y → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, MarginLossFunction ρ (MarginFunction h (S i) (f (S i)))

end FoundationsML.MultiClass
