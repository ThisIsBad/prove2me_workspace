import Mathlib

/-! Hart and Schmeidler (1989), §3, pp. 20–23. The player set may be uncountable. -/

namespace HartSchmeidler.FinStrat

open MeasureTheory Finset

variable {ι : Type*} {S : ι → Type*}

/-- Condition (3), p. 21, for a countably additive probability on the product σ-algebra.
The integrability clause excludes Lean's default value zero for an undefined integral. -/
def IsCorrelatedEq [DecidableEq ι] [∀ i, MeasurableSpace (S i)]
    (h : ι → (∀ i, S i) → ℝ) (μ : Measure (∀ i, S i)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (i : ι) (r t : S i),
      IntegrableOn (fun s => h i s - h i (Function.update s i t)) {s | s i = r} μ ∧
      0 ≤ ∫ s in {s | s i = r},
        (h i s - h i (Function.update s i t)) ∂μ

/-- An f-set of the proof of Theorem 2, pp. 22–23: a nonempty finite strategy set
at every coordinate, with only finitely many nonsingleton coordinates. -/
def IsFSet [∀ i, DecidableEq (S i)] (T : ∀ i, Finset (S i)) : Prop :=
  (∀ i, (T i).Nonempty) ∧ {i | ¬ ∃ a : S i, T i = {a}}.Finite

/-- Anchoring fixes the paper's nondirected index order: all f-sets contain the fixed profile. -/
def IsAnchoredFSet [∀ i, DecidableEq (S i)]
    (anchor : ∀ i, S i) (T : ∀ i, Finset (S i)) : Prop :=
  IsFSet T ∧ ∀ i, anchor i ∈ T i

/-- Pointwise inclusion of f-sets, i.e. inclusion of their products. -/
def FSetLE (T U : ∀ i, Finset (S i)) : Prop := ∀ i, T i ⊆ U i

/-- A finite weighted correlated equilibrium of the finite game Γ_T, viewed as a
finite weighted set of profiles in the unrestricted product S. -/
def IsFSetCE [DecidableEq ι] [∀ i, DecidableEq (S i)]
    (h : ι → (∀ i, S i) → ℝ) (T : ∀ i, Finset (S i))
    (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ) : Prop :=
  (∀ s ∈ F, ∀ i, s i ∈ T i) ∧
    (∀ s ∈ F, 0 ≤ w s) ∧
    (∑ s ∈ F, w s) = 1 ∧
    ∀ (i : ι) (r t : S i), r ∈ T i → t ∈ T i →
      0 ≤ ∑ s ∈ F.filter (fun s => s i = r),
        w s * (h i s - h i (Function.update s i t))

/-- The countably additive measure carried by a finite weighted set of profiles.
It is defined on the product σ-algebra even when the singleton of a profile is not measurable. -/
noncomputable def fsetMeasure [∀ i, MeasurableSpace (S i)]
    (F : Finset (∀ i, S i)) (w : (∀ i, S i) → ℝ) : Measure (∀ i, S i) :=
  ∑ s ∈ F, ENNReal.ofReal (w s) • Measure.dirac s

end HartSchmeidler.FinStrat
