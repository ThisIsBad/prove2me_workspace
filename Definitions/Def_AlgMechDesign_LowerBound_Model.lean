import Mathlib

namespace AlgMechDesign.LowerBound

open Finset

/-- A type vector `t` (Nisan–Ronen, Def. 10, pp. 175–176): `t i j` is the minimum time in which
agent `i : Fin n` can perform task `j : Fin k`. Types are positive. -/
def IsType {n k : ℕ} (t : Fin n → Fin k → ℝ) : Prop :=
  ∀ i j, 0 < t i j

/-- A single agent's type `tⁱ = (tⁱ_1, …, tⁱ_k)` is positive. -/
def IsAgentType {k : ℕ} (ti : Fin k → ℝ) : Prop :=
  ∀ j, 0 < ti j

/-- The set `xⁱ` of tasks that the allocation `x : Fin k → Fin n` (task `j` goes to agent `x j`)
gives to agent `i`. -/
def taskSet {n k : ℕ} (x : Fin k → Fin n) (i : Fin n) : Finset (Fin k) :=
  univ.filter (fun j => x j = i)

/-- The time `tⁱ(X) = ∑_{j ∈ X} tⁱ_j` an agent of type `ti` needs to perform all tasks of `X`
(Notation, p. 178). -/
def taskTime {k : ℕ} (ti : Fin k → ℝ) (X : Finset (Fin k)) : ℝ :=
  ∑ j ∈ X, ti j

/-- The load of agent `i` under the allocation `x`: `tⁱ(xⁱ) = ∑_{j ∈ xⁱ} tⁱ_j`. Agent `i`'s
valuation is `-load t x i`. -/
def load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) : ℝ :=
  taskTime (t i) (taskSet x i)

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j`, a maximum over the nonempty set of agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- Quasi-linear utility of agent `i` with true type `ti` in the direct mechanism
`(alloc, pay)` when the declaration profile is `d`: the payment handed to the agent minus the
true time it spends on the tasks allocated to it. -/
def utility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (d : Fin n → Fin k → ℝ) (i : Fin n)
    (ti : Fin k → ℝ) : ℝ :=
  pay d i - taskTime ti (taskSet (alloc d) i)

/-- Truthfulness (Def. 4) of a direct mechanism: for every positive declaration profile, every
agent, every positive true type and every positive misreport, reporting the true type gives at
least the utility of the misreport. -/
def IsTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ i : Fin n, ∀ ti ti' : Fin k → ℝ,
    IsAgentType ti → IsAgentType ti' →
      utility alloc pay (Function.update d i ti') i ti ≤
        utility alloc pay (Function.update d i ti) i ti

/-- `c`-approximation (Def. 2): on every positive type vector the chosen allocation has
make-span at most `c` times that of every allocation. -/
def IsApprox {n k : ℕ} [NeZero n] (c : ℝ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) :
    Prop :=
  ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin n,
    makespan t (alloc t) ≤ c * makespan t y

end AlgMechDesign.LowerBound
