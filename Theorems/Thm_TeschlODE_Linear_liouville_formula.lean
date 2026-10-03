import Mathlib
import Definitions.Def_TeschlODE_Linear_IsSolution

namespace TeschlODE.Linear

/-- Teschl, Lemma 3.11 (p. 83), Abel's identity / Liouville's formula (3.91): if the columns of
`U(t)` are `n` solutions of (3.79) on the interval `I`, the Wronski determinant
`W(t) = det U(t)` satisfies `W(t) = W(t₀) exp (∫_{t₀}^{t} tr A(s) ds)` for all `t₀, t ∈ I`. -/
theorem liouville_formula {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hA : ContinuousOn A I) (U : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hU : ∀ j : Fin n, IsSolution A I (fun t i => U t i j)) (t₀ t : ℝ) (ht₀ : t₀ ∈ I)
    (ht : t ∈ I) :
    (U t).det = (U t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by sorry

end TeschlODE.Linear

