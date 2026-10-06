import Mathlib

open Filter Topology

namespace MDPFinance.Semicontinuous

variable {E A : Type*} [TopologicalSpace E] [TopologicalSpace A]

/-- A set-valued mapping `x ↦ D(x)` is upper semicontinuous (Bäuerle–Rieder, Definition A.2.1a,
p. 351, PDF 358, Appendix A.2): for every `x`, if `xₙ → x` and `aₙ ∈ D(xₙ)` for all `n`, then
`(aₙ)` has an accumulation point in `D(x)`. Stated with sequences, exactly as the book's own
Appendix A.2 defines it (its own remark: "slightly more restrictive than other definitions
appearing in the literature", so Mathlib's neighborhood-filter-based `UpperHemicontinuous` for
correspondences is not used in its place — see `MODERATION_NOTES.md`). -/
def USCSetValued (D : E → Set A) : Prop :=
  ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    ∀ as : ℕ → A, (∀ n, as n ∈ D (xs n)) → ∃ a ∈ D x, MapClusterPt a atTop as

/-- A set-valued mapping `x ↦ D(x)` is lower semicontinuous (Bäuerle–Rieder, Definition A.2.1b,
p. 351, PDF 358): for every `x`, if `xₙ → x`, then every point of `D(x)` is an accumulation
point of some sequence `aₙ ∈ D(xₙ)`. -/
def LSCSetValued (D : E → Set A) : Prop :=
  ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    ∀ a ∈ D x, ∃ as : ℕ → A, (∀ n, as n ∈ D (xs n)) ∧ MapClusterPt a atTop as

/-- A set-valued mapping is continuous if it is upper and lower semicontinuous (Bäuerle–Rieder,
Definition A.2.1c, p. 351, PDF 358). -/
def ContinuousSetValued (D : E → Set A) : Prop :=
  USCSetValued D ∧ LSCSetValued D

end MDPFinance.Semicontinuous
