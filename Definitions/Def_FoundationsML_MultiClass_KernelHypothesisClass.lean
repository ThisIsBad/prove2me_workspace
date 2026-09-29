import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GroupNormLp

namespace FoundationsML.MultiClass

/-- The family `H_{K,p}` of multi-class kernel-based hypotheses with feature map `Φ : X → Hb`
and group-norm bound `Λ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*,
2nd ed., MIT Press 2018, p. 219, PDF p. 236):
`H_{K,p} = {(x,y) ↦ w_y · Φ(x) : W = (w_1,…,w_k), ‖W‖_{H,p} ≤ Λ}`. -/
def KernelHypothesisClass {X Hb : Type*} [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (Φ : X → Hb) (k : ℕ) (p Λ : ℝ) : Set (X × Fin k → ℝ) :=
  {h | ∃ W : Fin k → Hb, GroupNormLp p W ≤ Λ ∧
    h = fun xy => (inner (𝕜 := ℝ) (W xy.2) (Φ xy.1) : ℝ)}

end FoundationsML.MultiClass
