import Mathlib

namespace Supermodularity.Monotonicity

/-- `IncreasingDifferencesOn f S` says the real-valued function `f : X → T → ℝ` has
increasing differences in `(x, t)` on `S ⊆ X × T`: for every `t' ≺ t''` in `T`, the map
`x ↦ f x t'' - f x t'` is monotone on the intersection of the sections of `S` at `t'`
and at `t''`. -/
def IncreasingDifferencesOn {X T : Type*} [PartialOrder X] [PartialOrder T]
    (f : X → T → ℝ) (S : Set (X × T)) : Prop :=
  ∀ ⦃t' t'' : T⦄, t' < t'' →
    MonotoneOn (fun x : X => f x t'' - f x t')
      ({x : X | (x, t') ∈ S} ∩ {x : X | (x, t'') ∈ S})

end Supermodularity.Monotonicity
