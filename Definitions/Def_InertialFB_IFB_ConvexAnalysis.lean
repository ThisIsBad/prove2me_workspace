import Mathlib

open Filter Topology

namespace InertialFB.IFB

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A function `Φ : H → ℝ ∪ {+∞}` (encoded as `EReal`) is *proper* if it never takes the value
`-∞` and is not identically `+∞`. -/
def IsProperFn (Φ : H → EReal) : Prop :=
  (∀ x, Φ x ≠ ⊥) ∧ ∃ x, Φ x ≠ ⊤

/-- An extended-valued function `Φ : H → EReal` is *convex* if its epigraph
`{(x, t) ∈ H × ℝ | Φ x ≤ t}` is a convex subset of `H × ℝ`. -/
def IsConvexFn (Φ : H → EReal) : Prop :=
  Convex ℝ {p : H × ℝ | Φ p.1 ≤ (p.2 : EReal)}

/-- `g` is a subgradient of `Φ` at `u` (that is, `g ∈ ∂Φ(u)`, the convex subdifferential):
`Φ u` is finite from above (`u ∈ dom Φ`) and `Φ u + ⟪g, v - u⟫ ≤ Φ v` for every `v ∈ H`. -/
def IsSubgradient (Φ : H → EReal) (u g : H) : Prop :=
  Φ u ≠ ⊤ ∧ ∀ v : H, Φ u + ((inner ℝ g (v - u) : ℝ) : EReal) ≤ Φ v

/-- Weak convergence `u k ⇀ p` in the Hilbert space `H`: `⟪u k, v⟫ → ⟪p, v⟫` for every `v ∈ H`. -/
def WeakTendsto (u : ℕ → H) (p : H) : Prop :=
  ∀ v : H, Tendsto (fun k => inner ℝ (u k) v) atTop (𝓝 (inner ℝ p v))

/-- A map `F : H → H` is weak-to-weak sequentially continuous: whenever `x k ⇀ p`,
also `F (x k) ⇀ F p`. -/
def WeakSeqContinuous (F : H → H) : Prop :=
  ∀ (x : ℕ → H) (p : H), WeakTendsto x p → WeakTendsto (F ∘ x) (F p)

end InertialFB.IFB
