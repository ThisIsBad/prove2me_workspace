import Mathlib

namespace MDPFinance.StructuredModels

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `f` is convex on `s` (Bäuerle–Rieder uses ordinary convexity/concavity of real- and
`EReal`-valued functions throughout §2.4.4-2.4.5 without stating a numbered definition). Mathlib's
`ConvexOn` requires a `Module ℝ β` on the codomain, which `EReal` does not have (no `SMul ℝ EReal`
instance, since `EReal` is not a vector space); this restates the same defining inequality with
real scalars cast into `EReal` and multiplied there (`EReal` does carry a `Mul`), matching how
this chunk's other definitions already treat `EReal` arithmetic (see `MODERATION_NOTES.md`). -/
def ConvexOnEReal (s : Set E) (f : E → EReal) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

/-- `f` is concave on `s`, the `EReal`-valued analogue of `ConcaveOn`; see `ConvexOnEReal`. -/
def ConcaveOnEReal (s : Set E) (f : E → EReal) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    (a : EReal) * f x + (b : EReal) * f y ≤ f (a • x + b • y)

end MDPFinance.StructuredModels
