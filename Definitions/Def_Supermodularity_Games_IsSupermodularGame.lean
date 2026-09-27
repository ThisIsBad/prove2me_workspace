import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn

namespace Supermodularity.Games

/-- The projection `Sᵢ` of `S` onto player `i`'s strategies (Topkis p. 178): the
strategies `y` occurring as the `i`-th coordinate of some feasible joint strategy. -/
def proj {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (i : ι) : Set (Fin (m i) → ℝ) :=
  {y | ∃ x, Function.update x i y ∈ S}

/-- The projection `S₋ᵢ` of `S` onto the other players' strategies (Topkis p. 178),
represented by full joint strategies whose `i`-th coordinate is irrelevant. -/
def projOthers {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (i : ι) : Set (∀ i, Fin (m i) → ℝ) :=
  {x | ∃ y, Function.update x i y ∈ S}

/-- `IsSupermodularGame S f` says the noncooperative game with feasible joint
strategy set `S` and payoff functions `f` is a **supermodular game** (Topkis p. 178–179):
`S` is a sublattice of `ℝᵐ`; for each player `i` and each `x₋ᵢ ∈ S₋ᵢ` the payoff
`yᵢ ↦ fᵢ(yᵢ, x₋ᵢ)` is supermodular on the projection `Sᵢ`; and `fᵢ(yᵢ, x₋ᵢ)` has
increasing differences in `(yᵢ, x₋ᵢ)` on `Sᵢ × S₋ᵢ`. Other players' strategies enter
through `Function.update x i y`, whose `i`-th coordinate of `x` is overwritten. -/
structure IsSupermodularGame {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ) : Prop where
  sublattice : IsSublattice S
  supermodular : ∀ i, ∀ x ∈ projOthers S i,
    Supermodularity.Monotonicity.SupermodularOn
      (fun y : Fin (m i) → ℝ => f i (Function.update x i y)) (proj S i)
  increasing_differences : ∀ i : ι,
    Supermodularity.Monotonicity.IncreasingDifferencesOn
      (fun (y : Fin (m i) → ℝ) (x : ∀ i, Fin (m i) → ℝ) => f i (Function.update x i y))
      (proj S i ×ˢ projOthers S i)

end Supermodularity.Games
