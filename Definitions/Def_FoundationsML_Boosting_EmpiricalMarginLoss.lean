import Mathlib
import Definitions.Def_FoundationsML_Boosting_PhiRho

namespace FoundationsML.Boosting

/-- The empirical margin loss of a real-valued hypothesis `h` on a sample `S = (x_1,…,x_m)`
with labels `y = (y_1,…,y_m)` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 5.6, p. 92, PDF p. 109, restated locally for
this chapter): `R̂_{S,ρ}(h) = (1/m) ∑_{i=1}^m Φ_ρ(y_i h(x_i))`. -/
noncomputable def EmpiricalMarginLoss {X : Type*} {m : ℕ} (ρ : ℝ)
    (S : Fin m → X) (y : Fin m → ℝ) (h : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, PhiRho ρ (y i * h (S i))

end FoundationsML.Boosting
