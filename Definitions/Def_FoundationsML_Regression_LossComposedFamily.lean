import Mathlib

namespace FoundationsML.Regression

/-- The family of loss functions `G = {(x,y) ↦ L(h(x),y) : h ∈ H}` associated to a hypothesis
set `H` of real-valued functions and a loss `L : ℝ → ℝ → ℝ` (Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 269, PDF p. 286, also used in
Definition 11.4's `G`, p. 271, PDF p. 288). -/
def LossComposedFamily {X : Type*} (L : ℝ → ℝ → ℝ) (H : Set (X → ℝ)) : Set (X × ℝ → ℝ) :=
  {g | ∃ h ∈ H, g = fun p => L (h p.1) p.2}

end FoundationsML.Regression
