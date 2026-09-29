import Mathlib

/-!
# Cumulative distribution functions and limit permutations

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 3, Eq. (4) and Definition 1.3.

A definition bundle: the cdf predicate (4) and the class `𝒵` of limit permutations.

**Formalization Note.** The unit interval `[0, 1]` is Mathlib's `unitInterval` (written `I`), a
subtype of `ℝ` carrying the restriction of Lebesgue measure as `volume` (a probability measure).
Values of `Z` are taken in `ℝ`, and membership in `[0, 1]` is a clause of the definition.
-/

namespace PermLimits.Shared

open MeasureTheory unitInterval

/-- **cdf** (Hoppen et al., arXiv:1103.5844v2, Eq. (4), p. 3). A function `F : [0,1] → [0,1]`
is a cdf if it is non-decreasing and right-continuous with `F(0) ≥ 0` and `F(1) = 1`.

**Formalization Note.** `F` is real-valued; its values lie in `[0, 1]` as a consequence of
monotonicity, `F(0) ≥ 0` and `F(1) = 1`. Right-continuity at `y` is continuity within `[y, 1]`.
-/
def IsCDF (F : I → ℝ) : Prop :=
  Monotone F ∧ (∀ y : I, ContinuousWithinAt F (Set.Ici y) y) ∧ 0 ≤ F 0 ∧ F 1 = 1

/-- **Limit permutation** (Hoppen et al., arXiv:1103.5844v2, Definition 1.3, p. 3). A limit
permutation is a Lebesgue measurable function `Z : [0,1]² → [0,1]` such that
(a) for **every** `x ∈ [0,1]`, `Z(x, ·)` is a cdf (Eq. (4)), and
(b) for **every** `y ∈ [0,1]`, `∫₀¹ Z(x, y) dx = y`.
The set of limit permutations is `𝒵`.

**Formalization Note.** `Z` is curried, `Z x y = Z(x, y)`. "Lebesgue measurable" is
`AEMeasurable (Function.uncurry Z)` for the product Lebesgue measure `volume` on `I × I`; a
real function is almost-everywhere measurable exactly when it is measurable for the completed
(Lebesgue) σ-algebra. Conditions (a) and (b) are imposed pointwise for every `x` and every `y`, as
in the paper, not almost everywhere. The integral in (b) is the Bochner integral over `I` with
respect to Lebesgue measure. -/
def IsLimitPerm (Z : I → I → ℝ) : Prop :=
  AEMeasurable (Function.uncurry Z) (volume : Measure (I × I)) ∧
  (∀ x y : I, Z x y ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ x : I, IsCDF (Z x)) ∧
  (∀ y : I, ∫ x, Z x y = (y : ℝ))

end PermLimits.Shared
