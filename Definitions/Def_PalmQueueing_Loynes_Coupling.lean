import Mathlib

/-!
# Coupling and the distance in variation (§2.4.1, p.98)

Two definitions, both from p.98, and neither specific to queues: this is the general machinery
§2.4 uses to say in what sense a queue started from an arbitrary initial condition reaches its
stationary regime.
-/

namespace PalmQueueing.Loynes

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two stochastic processes `{X_n}` and `{Z_n}`, defined on the same probability space
`(Ω, F, P)`, **couple** (p.98) if there exists a finite random variable `N`, also defined on this
space, such that `X_n = Z_n` for all `n ≥ N`. The random variable `N` is the **coupling time**.

`N` is an `ℕ`-valued **random variable** (measurable), so its finiteness is carried by the type;
the book allows it to take values in `ℝ₊` or in `ℕ`, and the sequences it is used on are indexed by
`ℕ`. The equality `X_n = Z_n` for `n ≥ N` is required `P`-almost surely. -/
def Couple {E : Type*} (P : Measure Ω) (X Z : ℕ → Ω → E) : Prop :=
  ∃ N : Ω → ℕ, Measurable N ∧ ∀ᵐ ω ∂P, ∀ n : ℕ, N ω ≤ n → X n ω = Z n ω

/-- A sequence is **`θ`-compatible** when `Z_n = Z₀ ∘ θⁿ` for a measurable shift `θ`. -/
def IsShiftCompatible {E : Type*} (θ : Ω → Ω) (Z : ℕ → Ω → E) : Prop :=
  ∀ (n : ℕ) (ω : Ω), Z n ω = Z 0 (θ^[n] ω)

/-- The **distance in variation** of two probabilities on `(Ω, F)` (p.98):
`|P₁ − P₂| = sup_{A ∈ F} |P₁(A) − P₂(A)|`.

It is used below in its `ε`-`δ` form — one index serving every `A` at once — rather than as an
`iSup`, because that is literally what "converges in variation" asserts and it leaves no room for
a supremum to be read pointwise. -/
def variationLE {α : Type*} [MeasurableSpace α] (P₁ P₂ : Measure α) (ε : ℝ) : Prop :=
  ∀ A : Set α, MeasurableSet A → |(P₁ A).toReal - (P₂ A).toReal| ≤ ε

end PalmQueueing.Loynes
