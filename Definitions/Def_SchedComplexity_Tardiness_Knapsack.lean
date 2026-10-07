import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_OneMachine_Knapsack

namespace SchedComplexity.Tardiness

open CookPvsNP ProjSchedTW.Complexity

/-- KNAPSACK (Brucker, Lenstra & Rinnooy Kan 1975, Theorem 2(b), p. 14): given sizes
`a_1, …, a_t` (here `a : Fin t → ℕ`, 0-based) and `b`, is there a subset `S` of
`T = {1, …, t}` with `Σ_{j ∈ S} a_j = b`? The positivity of the data is not part of this
predicate. The KNAPSACK language, with positivity as a membership condition, is
`SchedComplexity.OneMachine.knapsackLang` (imported above), stated with the list form
`SchedComplexity.OneMachine.KnapsackYes`; `KnapsackYes a b` holds iff
`SchedComplexity.OneMachine.KnapsackYes (List.ofFn a) b` does. -/
def KnapsackYes {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : Prop :=
  ∃ S : Finset (Fin t), ∑ j ∈ S, a j = b

end SchedComplexity.Tardiness
