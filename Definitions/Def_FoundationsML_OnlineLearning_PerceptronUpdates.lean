import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronWeight

open Classical

namespace FoundationsML.OnlineLearning

/-- The set `I` of round indices `t ∈ [T]` (here `t < T`, 0-indexed) at which the Perceptron
algorithm makes an update while processing `x_1,…,x_T` with labels `y_1,…,y_T` (Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 196,
PDF p. 213, Theorem 8.11's own `I`). -/
noncomputable def PerceptronUpdates {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t => y t * (inner (𝕜 := ℝ) (PerceptronWeight x y t) (x t) : ℝ) ≤ 0)

end FoundationsML.OnlineLearning
