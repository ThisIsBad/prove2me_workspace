import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_Tardiness_Knapsack

namespace SchedComplexity.TotalCompletion

open ProjSchedTW.Complexity (BSym encNats)

/-- KNAPSACK (Brucker, Lenstra & Rinnooy Kan 1975, Theorem 2(b), p. 14): the numbers
`a_1, …, a_t, b` are an instance when they are positive integers. The items are indexed by
`Fin t` (0-based: index `i` is the paper's `a_{i+1}`). -/
def IsKnapsackInstance {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ 0 < b

/-- The code of a KNAPSACK instance: the numbers `b, a_1, …, a_t` in binary (`encNats`). The
code determines `(t, a, b)`: separators delimit the numbers, the first is `b`, and the number of
remaining ones is `t`. -/
def knapsackCode {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : List BSym :=
  encNats (b :: List.ofFn a)

/-- The KNAPSACK language: codes of the instances (all of `a_1, …, a_t, b` positive) that have a
solution. Codes of instances with a zero entry are not in the language. -/
def knapsackLang : CookPvsNP.Lang BSym :=
  { x | ∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
      IsKnapsackInstance a b ∧ SchedComplexity.Tardiness.KnapsackYes a b ∧ x = knapsackCode a b }

end SchedComplexity.TotalCompletion
