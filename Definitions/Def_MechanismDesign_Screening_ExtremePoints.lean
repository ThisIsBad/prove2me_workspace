import Mathlib

/-!
# Extreme points and the set `M` of increasing allocation rules (Börgers, Ch. 2, pp.15–16)

* Definition 2.4 (p.16): extreme points of a convex subset of a vector space.
* The space `F` of bounded functions `[θ̲, θ̄] → ℝ` with the `L¹` norm `∫ |f| dμ` (pp.15–16),
  and the subset `M` of increasing functions with values in `[0, 1]`.

The `L¹` "norm" vanishes on every function that is zero almost everywhere, so it is a norm only
on almost-everywhere equivalence classes. `F` is therefore modelled as the Lebesgue space
`L¹([θ̲, θ̄])` (`MeasureTheory.Lp ℝ 1` for Lebesgue measure restricted to `[θ̲, θ̄]`), a genuine
normed space, and `M` as the set of classes having an increasing representative with values in
`[0, 1]`. This is the reading the book itself adopts in notes 4–6 (p.235) to Lemma 2.7.
-/

namespace MechanismDesign.Screening

open MeasureTheory

/-- **Extreme point** (Definition 2.4, p.16): if `C` is a (convex) subset of a vector space `X`,
then `x ∈ C` is an extreme point of `C` if for every `y ∈ X` with `y ≠ 0`, either `x + y ∉ C` or
`x − y ∉ C` (or both). -/
def IsExtremePoint {X : Type*} [AddCommGroup X] (C : Set X) (x : X) : Prop :=
  x ∈ C ∧ ∀ y : X, y ≠ 0 → x + y ∉ C ∨ x - y ∉ C

/-- Lebesgue measure `μ` restricted to the type interval `[θ̲, θ̄]`. -/
noncomputable abbrev typeMeasure (θlo θhi : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc θlo θhi)

/-- The space `F` of p.15–16, as the normed space `L¹([θ̲, θ̄], μ)`: the norm of `f` is
`∫_{θ̲}^{θ̄} |f| dμ`. -/
abbrev L1Space (θlo θhi : ℝ) : Type :=
  Lp ℝ 1 (typeMeasure θlo θhi)

/-- The set `M ⊂ F` (p.16) of increasing functions with values in `[0, 1]`: the classes in
`L¹([θ̲, θ̄])` that have a representative `q` which is (weakly) increasing on `[θ̲, θ̄]` and
satisfies `q(x) ∈ [0, 1]` for all `x ∈ [θ̲, θ̄]`. -/
def monotoneAllocations (θlo θhi : ℝ) : Set (L1Space θlo θhi) :=
  {g | ∃ q : ℝ → ℝ, MonotoneOn q (Set.Icc θlo θhi) ∧
    (∀ x ∈ Set.Icc θlo θhi, q x ∈ Set.Icc (0 : ℝ) 1) ∧
    (g : ℝ → ℝ) =ᵐ[typeMeasure θlo θhi] q}

end MechanismDesign.Screening
