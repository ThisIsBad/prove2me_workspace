import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace Filter Topology NNReal ENNReal

namespace ThreeOpSplitting.Convergence

/-- `A` is uniformly monotone on the set `S`: there is a nondecreasing
`φ : [0, ∞) → [0, +∞]` with `φ 0 = 0` that vanishes only at `0`, such that
`⟪x - y, u - v⟫ ≥ φ(‖x - y‖)` for all `x, y ∈ S`, `u ∈ A x`, `v ∈ A y`. -/
def IsUniformlyMonotoneOn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (S : Set H) : Prop :=
  ∃ φ : ℝ≥0 → ℝ≥0∞, Monotone φ ∧ φ 0 = 0 ∧ (∀ t, φ t = 0 → t = 0) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ u ∈ A x, ∀ v ∈ A y,
      ((φ ‖x - y‖₊ : ℝ≥0∞) : EReal) ≤ ((⟪x - y, u - v⟫_ℝ : ℝ) : EReal)

/-- `A` is uniformly monotone on every nonempty bounded subset of `dom(A)`
(the function `φ` may depend on the subset). -/
def IsUniformlyMonotoneOnBounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) : Prop :=
  ∀ S : Set H, S ⊆ dom A → S.Nonempty → Bornology.IsBounded S → IsUniformlyMonotoneOn A S

/-- A single-valued operator `C` is demiregular at `x`: every sequence `x k ⇀ x` with
`C (x k) → C x` (strongly) converges strongly to `x`. -/
def IsDemiregularAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : H → H) (x : H) : Prop :=
  ∀ xs : ℕ → H, WeakTendsto xs x → Tendsto (fun k => C (xs k)) atTop (𝓝 (C x)) →
    Tendsto xs atTop (𝓝 x)

end ThreeOpSplitting.Convergence
