import Mathlib

namespace PolicyGradTheory.ProjGA

/-- `Proj` is a Euclidean projection onto `C`: for every `z`, the point `Proj z` lies in `C` and is a
point of `C` nearest to `z` in the norm (the projection `P_{∆(A)^{|S|}}` of (9), arXiv:1908.00261v5,
§4.2, p. 15, and `P_C` of (55), App. E, p. 77). For a nonempty closed convex `C` in a Euclidean space
the nearest point exists and is unique, so the predicate determines `Proj`. -/
def IsProjOnto {E : Type*} [NormedAddCommGroup E] (C : Set E) (Proj : E → E) : Prop :=
  ∀ z : E, Proj z ∈ C ∧ ∀ y ∈ C, ‖z - Proj z‖ ≤ ‖z - y‖

end PolicyGradTheory.ProjGA
