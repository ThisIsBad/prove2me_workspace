import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Robinson (1951), p. 297, Lemma 1: `lim inf_{t→∞} (max V(t) − min U(t))/t ≥ 0`, stated in
ε-form: for every `ε > 0`, eventually `(max V(t) − min U(t))/t ≥ −ε`. -/
theorem lemma1 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, -ε ≤ (vmax (V t) - vmin (U t)) / t := by sorry

end RobinsonFP.Convergence

