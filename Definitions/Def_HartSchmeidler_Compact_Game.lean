import Mathlib

namespace HartSchmeidler.Compact

open MeasureTheory

/-- The space `S = ∏_{i ∈ N} Sⁱ` of pure-strategy profiles. It is a type synonym of the
dependent function type so that it can carry the paper's σ-algebra `Σ`, the Borel σ-algebra of
the product topology, instead of Mathlib's product σ-algebra `Σ₀ = ⊗ Σⁱ` (footnote 13). -/
def Profile {ι : Type*} (S : ι → Type*) : Type _ := ∀ i, S i

namespace Profile

variable {ι : Type*} {S : ι → Type*}

/-- `S` carries the product topology. -/
instance instTopologicalSpace [∀ i, TopologicalSpace (S i)] : TopologicalSpace (Profile S) :=
  Pi.topologicalSpace

instance instCompactSpace [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] :
    CompactSpace (Profile S) :=
  inferInstanceAs (CompactSpace (∀ i, S i))

instance instT2Space [∀ i, TopologicalSpace (S i)] [∀ i, T2Space (S i)] :
    T2Space (Profile S) :=
  inferInstanceAs (T2Space (∀ i, S i))

instance instNonempty [∀ i, Nonempty (S i)] : Nonempty (Profile S) :=
  inferInstanceAs (Nonempty (∀ i, S i))

/-- `Σ` is the Borel σ-algebra of the product topology on `S`. -/
instance instMeasurableSpace [∀ i, TopologicalSpace (S i)] : MeasurableSpace (Profile S) :=
  borel (Profile S)

instance instBorelSpace [∀ i, TopologicalSpace (S i)] : BorelSpace (Profile S) :=
  ⟨rfl⟩

end Profile

variable {ι : Type*} [DecidableEq ι] {S : ι → Type*}

/-- Condition (4), p. 23: a correlated equilibrium with respect to `{Σⁱ}` and `Σ` (here `Σ` is the
Borel σ-algebra of `S`) is a probability measure `μ` on `S` such that for every player `i` and
every `Σⁱ`-measurable `ζ : Sⁱ → Sⁱ`, the gain from obeying the recommendation,
`hⁱ(s⁻ⁱ, sⁱ) − hⁱ(s⁻ⁱ, ζ(sⁱ))`, is `μ`-integrable with nonnegative integral. -/
def IsCorrelatedEq [∀ i, TopologicalSpace (S i)] [∀ i, MeasurableSpace (S i)]
    (h : ι → Profile S → ℝ) (μ : Measure (Profile S)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (i : ι) (ζ : S i → S i), Measurable ζ →
      Integrable (fun s : Profile S => h i s - h i (Function.update s i (ζ (s i)))) μ ∧
        0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂μ

/-- An f-set (p. 24): `T = ∏ Tⁱ` with every `Tⁱ` a nonempty finite subset of `Sⁱ`, and `Tⁱ` a
singleton for all but finitely many players `i`. -/
def IsFSet (T : ∀ i, Finset (S i)) : Prop :=
  (∀ i, (T i).Nonempty) ∧ {i : ι | (T i).card ≠ 1}.Finite

/-- An f-set anchored at the profile `ŝ`: it contains `ŝ`, i.e. `ŝⁱ ∈ Tⁱ` for every `i`. The
anchored f-sets are directed under coordinatewise inclusion. -/
def IsAnchoredFSet (ŝ : Profile S) (T : ∀ i, Finset (S i)) : Prop :=
  IsFSet T ∧ ∀ i, ŝ i ∈ T i

open Classical in
/-- A correlated equilibrium `q_T` of the finite game `Γ_T` (p. 24), regarded as a probability
measure on `S` with finite support inside `T`: a finite set `F` of profiles of `T` with weights
`w ≥ 0` summing to one, satisfying condition (1) of `Γ_T`: for every player `i` and all
`r, t ∈ Tⁱ`, `∑_{s ∈ F, sⁱ = r} w(s) [hⁱ(s) − hⁱ(s⁻ⁱ, t)] ≥ 0`. -/
def IsFSetCE (h : ι → Profile S → ℝ) (T : ∀ i, Finset (S i)) (F : Finset (Profile S))
    (w : Profile S → ℝ) : Prop :=
  (∀ s ∈ F, ∀ i, s i ∈ T i) ∧ (∀ s ∈ F, 0 ≤ w s) ∧ ∑ s ∈ F, w s = 1 ∧
    ∀ (i : ι), ∀ r ∈ T i, ∀ t ∈ T i,
      0 ≤ ∑ s ∈ F.filter (fun s : Profile S => s i = r),
        w s * (h i s - h i (Function.update s i t))

open Classical in
/-- The deviation of the special case (p. 24): `ζ(x) = t` for `x ∈ R` and `ζ(x) = x` otherwise. -/
noncomputable def specialDeviation {α : Type*} (t : α) (R : Set α) : α → α :=
  fun x => if x ∈ R then t else x

end HartSchmeidler.Compact
