import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Invariance

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- A `(δ,T)`-pseudo-orbit from `a` to `b` (Benaïm 1999, p. 21), given by its length `k`, its
points `y 0, …, y k` and its times `t 0, …, t (k-1)`: there is at least one partial trajectory
(`1 ≤ k`), every time satisfies `t_i ≥ T`, `d(y_0, a) < δ`, `d(Φ_{t_j}(y_j), y_{j+1}) < δ` for
`j = 0, …, k-1`, and `y_k = b` exactly. -/
def IsPseudoOrbit {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (δ : ℝ) (T : ℝ≥0) (a b : X)
    (k : ℕ) (y : ℕ → X) (t : ℕ → ℝ≥0) : Prop :=
  1 ≤ k ∧ (∀ i < k, T ≤ t i) ∧ dist (y 0) a < δ ∧
    (∀ j < k, dist (Φ (t j) (y j)) (y (j + 1)) < δ) ∧ y k = b

/-- `a ↪_{δ,T} b`: there exists a `(δ,T)`-pseudo-orbit from `a` to `b`. -/
def PseudoOrbitTo {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (δ : ℝ) (T : ℝ≥0) (a b : X) :
    Prop :=
  ∃ (k : ℕ) (y : ℕ → X) (t : ℕ → ℝ≥0), IsPseudoOrbit Φ δ T a b k y t

/-- `a ↪ b`: `a ↪_{δ,T} b` for every `δ > 0` and `T > 0`. -/
def ChainTo {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (a b : X) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ T : ℝ≥0, 0 < T → PseudoOrbitTo Φ δ T a b

/-- `R(Φ)`, the set of chain recurrent points `a ↪ a`. -/
def chainRecurrentSet {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) : Set X :=
  {a | ChainTo Φ a a}

/-- An *internally chain recurrent* set (p. 21): a nonempty compact invariant set `Λ` such that
every point of `Λ` is chain recurrent for the restricted semiflow `Φ|Λ` (pseudo-orbits of `Φ|Λ`
have all their points in `Λ`). -/
def IsInternallyChainRecurrent {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Λ : Set M) :
    Prop :=
  Λ.Nonempty ∧ IsCompact Λ ∧
    ∃ h : IsInvariantSet Φ Λ, ∀ p : Λ, ChainTo (restrictSemiflow Φ h) p p

/-- An *internally chain transitive* set (p. 21): a nonempty compact invariant set `Λ` such that
`Φ|Λ` is chain transitive, i.e. `a ↪ b` for `Φ|Λ` for all `a, b ∈ Λ`. -/
def IsInternallyChainTransitive {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Λ : Set M) :
    Prop :=
  Λ.Nonempty ∧ IsCompact Λ ∧
    ∃ h : IsInvariantSet Φ Λ, ∀ a b : Λ, ChainTo (restrictSemiflow Φ h) a b

end StochApproxDyn.LimitSet
