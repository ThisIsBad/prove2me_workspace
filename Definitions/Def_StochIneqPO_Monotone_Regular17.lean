import Mathlib

namespace StochIneqPO.Monotone

open Filter Topology

/-- **Condition (17)** (Kamae–Krengel–O'Brien 1977, Theorem 6, p. 908). A topological space `E`
with a partial order satisfies (17) if for all sequences `(xₙ)`, `(yₙ)` in `E` with
`xₙ ≤ yₙ ≤ xₙ₊₁` for every `n`, convergence `xₙ → z` implies `yₙ → z`.
The paper indexes from `n = 1`; here sequences are indexed by `ℕ` from `0`. -/
def Regular17 (E : Type*) [TopologicalSpace E] [PartialOrder E] : Prop :=
  ∀ (x y : ℕ → E) (z : E), (∀ n, x n ≤ y n ∧ y n ≤ x (n + 1)) →
    Tendsto x atTop (𝓝 z) → Tendsto y atTop (𝓝 z)

end StochIneqPO.Monotone
