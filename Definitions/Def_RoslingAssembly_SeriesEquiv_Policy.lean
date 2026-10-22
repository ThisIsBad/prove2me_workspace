import Mathlib

namespace RoslingAssembly.SeriesEquiv

/-- A deterministic decision rule at period `k + 1`, using exactly the `k` demands
already observed. The output is indexed by an item number. -/
abbrev Policy : Type := (k : ℕ) → (Fin k → ℝ) → ℕ → ℝ

/-- The decision for item `i` in the paper's period `t`, along the demand path `ω`.
Lean coordinate `j` of `ω` is the paper's demand `ξ_(j+1)`. -/
def decision (π : Policy) (ω : ℕ → ℝ) (i t : ℕ) : ℝ :=
  π (t - 1) (fun j => ω j.val) i

/-- Every coordinate decision is measurable in its finite demand history. -/
def MeasurablePolicy (π : Policy) : Prop :=
  ∀ k i, Measurable (fun h : Fin k → ℝ => π k h i)

end RoslingAssembly.SeriesEquiv
