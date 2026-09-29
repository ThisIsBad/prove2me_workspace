import Mathlib

namespace BiconvexProg.BranchBound

/-- The convex envelope `Vex_Ω f` of `f` over `Ω` (Al-Khayyal–Falk 1983, p. 275): the pointwise
supremum of all functions `g` that are convex on `Ω` and underestimate `f` on `Ω`.
Evaluated at `z`, it is the real supremum of the values `g z` over all such `g`.

Junk values (real `sSup`): the value is meaningful only at points `z ∈ Ω` where some convex
minorant exists (then the set of values is nonempty and bounded above by `f z`). Off `Ω` the
values `g z` are unconstrained, the set is unbounded, and `sSup` returns `0`; if `Ω` is not
convex, no `g` is `ConvexOn` it and the value is `sSup ∅ = 0`. -/
noncomputable def convexEnvelope {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Ω : Set E) (f : E → ℝ) (z : E) : ℝ :=
  sSup {r : ℝ | ∃ g : E → ℝ, ConvexOn ℝ Ω g ∧ (∀ w ∈ Ω, g w ≤ f w) ∧ r = g z}

end BiconvexProg.BranchBound
