import Mathlib

namespace ProcessingNetworks.ProportionalFairness

open Classical

/-- The concave-optimization-problem domain (Section 10.1, before Eq. (10.1)): `A ⊂ ℝ^I_+` is
bounded, closed, convex, monotone (10.1) (downward-closed among nonnegative vectors), and
nontrivial (contains a strictly positive point). Restated identically from mission IX. -/
def IsPFDomain {I : ℕ} (AllocSet : Set (Fin I → ℝ)) : Prop :=
  Bornology.IsBounded AllocSet ∧ IsClosed AllocSet ∧ Convex ℝ AllocSet ∧
    (∀ x ∈ AllocSet, ∀ y : Fin I → ℝ, (∀ i, 0 ≤ y i) → y ≤ x → y ∈ AllocSet) ∧
    ∃ x ∈ AllocSet, ∀ i, 0 < x i

/-- The extended logarithm implementing the book's convention `log(0) = -∞` (Eq. 10.2). Restated
identically from mission IX (`09-proportional-fairness-core`): this chunk shares the
`ProcessingNetworks.ProportionalFairness` sub-namespace with mission IX but cannot import its
draft, so per this series' restate-not-import convention the definitions this chunk needs are
duplicated here, matching mission IX's own code exactly for a moderator to reconcile at upload
time. -/
noncomputable def extLog (x : ℝ) : EReal :=
  if x = 0 then ⊥ else (Real.log x : EReal)

/-- The objective `f(z,x) := ∑_i z_i log(x_i)` (Eq. 10.2), restated identically from mission IX. -/
noncomputable def f {I : ℕ} (z x : Fin I → ℝ) : EReal :=
  ∑ i, (z i : EReal) * extLog (x i)

/-- `x` is a maximizer of `f(z,·)` over `AllocSet`, restated identically from mission IX. -/
def IsPFMaximizer {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (z x : Fin I → ℝ) : Prop :=
  x ∈ AllocSet ∧ ∀ y ∈ AllocSet, f z y ≤ f z x

/-- The PF allocation function `ψ` (Eqs. 10.4-10.5), restated identically from mission IX. -/
noncomputable def psi {I : ℕ} (AllocSet : Set (Fin I → ℝ)) (z : Fin I → ℝ) : Fin I → ℝ :=
  fun i =>
    if 0 < z i then
      (if h : ∃ x, IsPFMaximizer AllocSet z x then (Classical.choose h) i else 0)
    else 0

/-- The group-level aggregate `a_ℓ(x) := ∑_{i ∈ I(ℓ)} x_i` (Eq. 10.22), restated identically from
mission IX, given a demand-group assignment `grp : Fin I → Fin L`. -/
def groupAggregate {I L : ℕ} (grp : Fin I → Fin L) (x : Fin I → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => grp i = ℓ), x i

end ProcessingNetworks.ProportionalFairness
