import Mathlib

namespace Supermodularity.Games

/-- `IsEquilibrium S f x'` says `x'` is an equilibrium point of the noncooperative
game with feasible joint strategy set `S` and payoff functions `f`: `x'` is
feasible, and no player `i` can strictly improve `f i` by unilaterally deviating
to any other feasible strategy `y`, the other players' strategies (`x'` with its
`i`-th coordinate overwritten) held fixed. -/
def IsEquilibrium {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ) : Prop :=
  x' ∈ S ∧ ∀ i, ∀ y : Fin (m i) → ℝ, Function.update x' i y ∈ S →
    f i (Function.update x' i y) ≤ f i x'

end Supermodularity.Games
