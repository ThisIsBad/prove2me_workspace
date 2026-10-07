import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.OneMachine

open CookPvsNP ProjSchedTW.Complexity

/-- A KNAPSACK instance (Brucker, Lenstra & Rinnooy Kan, Report BW 43/75, p. 14, Theorem 2(b)):
the list `a = [a_1, …, a_t]` (so `T = {1, …, t}` is `Fin a.length`, 0-based) and the target `b`.
It is a yes-instance iff some subset `S ⊆ T` has `∑_{j ∈ S} a_j = b`. Positivity of the data is
not part of this predicate; it is imposed by `knapsackLang`. -/
def KnapsackYes (a : List ℕ) (b : ℕ) : Prop :=
  ∃ S : Finset (Fin a.length), ∑ j ∈ S, a.get j = b

/-- The KNAPSACK language (Theorem 2(b), p. 14): the binary codes `b a_1 … a_t` (each number in
binary by `encNat`, one after the other) of the yes-instances whose data `a_1, …, a_t, b` are all
**positive** integers, as the paper's "Given positive integers a_1, …, a_t, b" requires. -/
def knapsackLang : Lang BSym :=
  { x | ∃ (a : List ℕ) (b : ℕ), (∀ v ∈ a, 0 < v) ∧ 0 < b ∧ KnapsackYes a b ∧
      x = encNats (b :: a) }

end SchedComplexity.OneMachine
