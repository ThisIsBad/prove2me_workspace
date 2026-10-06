import Mathlib

namespace AlgMechDesign.Randomized

open Finset

/-- A type vector `t` (Nisan–Ronen, Def. 10, pp. 175–176): `t i j` is the minimum time in which
agent `i : Fin n` can perform task `j : Fin k`. Types are positive. -/
def IsType {n k : ℕ} (t : Fin n → Fin k → ℝ) : Prop :=
  ∀ i j, 0 < t i j

/-- A single agent's type `tⁱ = (tⁱ_1, …, tⁱ_k)` is positive. -/
def IsAgentType {k : ℕ} (ti : Fin k → ℝ) : Prop :=
  ∀ j, 0 < ti j

/-- The load of agent `i` under the allocation `x : Fin k → Fin n` (task `j` goes to agent `x j`):
`tⁱ(xⁱ) = ∑_{j ∈ xⁱ} tⁱ_j`. Agent `i`'s valuation is `-load t x i`. -/
def load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => x j = i), t i j

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j`, a maximum over the nonempty set of agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- Quasi-linear utility of agent `i` with true type `ti` in the direct mechanism
`(alloc, pay)` when the declaration profile is `d`: the payment handed to the agent minus the
true time it spends on the tasks allocated to it. -/
def utility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (d : Fin n → Fin k → ℝ) (i : Fin n)
    (ti : Fin k → ℝ) : ℝ :=
  pay d i - ∑ j ∈ univ.filter (fun j => alloc d j = i), ti j

/-- Truthfulness (Def. 4): for every positive declaration profile of the others, every agent,
every positive true type and every positive misreport, reporting the true type gives at least
the utility of the misreport. -/
def IsTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ i : Fin n, ∀ ti ti' : Fin k → ℝ,
    IsAgentType ti → IsAgentType ti' →
      utility alloc pay (Function.update d i ti') i ti ≤
        utility alloc pay (Function.update d i ti) i ti

/-- Strong truthfulness (Def. 5): truthful, and every positive misreport `ti' ≠ ti` is strictly
worse than the truth for some positive declarations of the others; given truthfulness this says
that truth-telling is the only dominant strategy. -/
def IsStronglyTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  IsTruthful alloc pay ∧
    ∀ i : Fin n, ∀ ti ti' : Fin k → ℝ, IsAgentType ti → IsAgentType ti' → ti' ≠ ti →
      ∃ d : Fin n → Fin k → ℝ, IsType d ∧
        utility alloc pay (Function.update d i ti') i ti <
          utility alloc pay (Function.update d i ti) i ti

/-- Universal truthfulness (Def. 16) of a randomized mechanism (Def. 15) whose distribution has
full support on the index set `R` (as the uniform distribution does): the mechanism
`(alloc r, pay r)` is truthful for every `r ∈ R`, i.e. truth-telling is dominant for every
outcome of the coin tosses. -/
def IsUniversallyTruthful {n k : ℕ} {R : Type*}
    (alloc : R → (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : R → (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ r : R, IsTruthful (alloc r) (pay r)

/-- Universal strong truthfulness (Def. 16): universally truthful, and truth-telling is the only
universally dominant strategy — every positive misreport `ti' ≠ ti` fails to be dominant in some
mechanism `r` of the support, i.e. (given truthfulness of `r`) it is strictly worse than the
truth for some positive declarations of the others under `r`. -/
def IsUniversallyStronglyTruthful {n k : ℕ} {R : Type*}
    (alloc : R → (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : R → (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  IsUniversallyTruthful alloc pay ∧
    ∀ i : Fin n, ∀ ti ti' : Fin k → ℝ, IsAgentType ti → IsAgentType ti' → ti' ≠ ti →
      ∃ r : R, ∃ d : Fin n → Fin k → ℝ, IsType d ∧
        utility (alloc r) (pay r) (Function.update d i ti') i ti <
          utility (alloc r) (pay r) (Function.update d i ti) i ti

end AlgMechDesign.Randomized
