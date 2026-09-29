import Mathlib
import Definitions.Def_FoundationsML_Boosting_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_Boosting_ConvHull

namespace FoundationsML.Boosting

/-- Lemma 7.4 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT
Press 2018, p. 157, PDF p. 174). Let `H` be a set of functions mapping from `X` to `ℝ`. Then,
for any sample `S`, `R̂_S(conv(H)) = R̂_S(H)`. -/
theorem rademacher_complexity_conv_hull {X : Type*} {m : ℕ}
    (H : Set (X → ℝ)) (S : Fin m → X) :
    EmpiricalRademacherComplexity (ConvHull H) S = EmpiricalRademacherComplexity H S := by sorry

end FoundationsML.Boosting
