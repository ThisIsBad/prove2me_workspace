import Mathlib
import Definitions.Def_Supermodularity_Games_BestResponse

namespace Supermodularity.Games

/-- `BestJointResponse S f x` is the best joint response correspondence
`Y(x) = ×_{i ∈ N} Y_i(x_{-i})`: the set of joint strategies `x'` each of whose
components `x' i` is a best response for player `i` given the reference point
`x` (whose own `i`-th coordinate is ignored, as in `BestResponse`). -/
def BestJointResponse {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x : ∀ i, Fin (m i) → ℝ) : Set (∀ i, Fin (m i) → ℝ) :=
  {x' : ∀ i, Fin (m i) → ℝ | ∀ i, x' i ∈ BestResponse S f i x}

end Supermodularity.Games
