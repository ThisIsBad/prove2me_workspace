import Mathlib

namespace Supermodularity.Games

/-- `BestResponse S f i x` is player `i`'s best-response set `Y_i(x_{-i})` in the
noncooperative game with feasible joint strategy set `S` and payoff functions `f`:
the set of `y` maximizing `f i` over the feasible section of `S` at `x_{-i}`, where
`x` supplies the other players' strategies and its own `i`-th coordinate is
ignored (overwritten by `y`). -/
def BestResponse {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (i : ι) (x : ∀ i, Fin (m i) → ℝ) : Set (Fin (m i) → ℝ) :=
  {y : Fin (m i) → ℝ | Function.update x i y ∈ S ∧
    ∀ z : Fin (m i) → ℝ, Function.update x i z ∈ S →
      f i (Function.update x i z) ≤ f i (Function.update x i y)}

end Supermodularity.Games
