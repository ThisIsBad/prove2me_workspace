import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

open Finset

/-- Utility of agent `i` with true type `ti` in a general mechanism `(o, p)` (Def. 3,
pp. 171–172) when the strategy profile is `b`: agent `i` has strategy set `A i`, the output
`o b` is an allocation of the `k` tasks, and `p b i` is the payment handed to agent `i`. The
utility is `vⁱ(tⁱ, o) + pⁱ` with `vⁱ(tⁱ, o) = -tⁱ(oⁱ)`. -/
def genUtility {n k : ℕ} {A : Fin n → Type*} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) (b : (i : Fin n) → A i) (i : Fin n)
    (ti : Fin k → ℝ) : ℝ :=
  p b i - taskTime ti (taskSet (o b) i)

/-- The strategy `ai ∈ Aⁱ` is dominant for agent `i` of type `ti` (Def. 3, item 4): for every
strategy profile `a⁻ⁱ` of the other agents (dominant or not) and every alternative strategy
`a'ⁱ`, playing `ai` gives agent `i` at least the utility of playing `a'ⁱ`. -/
def IsDominant {n k : ℕ} {A : Fin n → Type*} (o : ((i : Fin n) → A i) → (Fin k → Fin n))
    (p : ((i : Fin n) → A i) → Fin n → ℝ) (i : Fin n) (ti : Fin k → ℝ) (ai : A i) : Prop :=
  ∀ a : (j : Fin n) → A j, ∀ ai' : A i,
    genUtility o p (Function.update a i ai') i ti ≤ genUtility o p (Function.update a i ai) i ti

/-- The mechanism `(o, p)` implements a `c`-approximation for task scheduling with dominant
strategies (Def. 3, item 4, with the specification of Def. 2): every agent of every positive
type has a dominant strategy, and for every positive type vector `t` and every tuple `a` of
dominant strategies for `t`, the output `o a` has make-span at most `c` times that of every
allocation. -/
def Implements {n k : ℕ} [NeZero n] {A : Fin n → Type*}
    (o : ((i : Fin n) → A i) → (Fin k → Fin n)) (p : ((i : Fin n) → A i) → Fin n → ℝ)
    (c : ℝ) : Prop :=
  (∀ i : Fin n, ∀ ti : Fin k → ℝ, IsAgentType ti → ∃ ai : A i, IsDominant o p i ti ai) ∧
    ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ a : (i : Fin n) → A i,
      (∀ i, IsDominant o p i (t i) (a i)) →
        ∀ y : Fin k → Fin n, makespan t (o a) ≤ c * makespan t y

end AlgMechDesign.LowerBound
