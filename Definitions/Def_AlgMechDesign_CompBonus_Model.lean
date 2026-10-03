import Mathlib

namespace AlgMechDesign.CompBonus

open Finset

/-- A type vector `t` (Nisan–Ronen, Def. 10, pp. 175–176): `t i j` is the minimum time in which
agent `i : Fin n` can perform task `j : Fin k`. Types are positive. -/
def IsType {n k : ℕ} (t : Fin n → Fin k → ℝ) : Prop :=
  ∀ i j, 0 < t i j

/-- A single agent's type (or declaration) `tⁱ = (tⁱ_1, …, tⁱ_k)` is positive. -/
def IsAgentType {k : ℕ} (ti : Fin k → ℝ) : Prop :=
  ∀ j, 0 < ti j

/-- The load of agent `i` under the allocation `x : Fin k → Fin n` (task `j` goes to agent `x j`)
for the type vector `t`: `∑_{j ∈ xⁱ} tⁱ_j`. -/
def load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => x j = i), t i j

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j` (Def. 10), a maximum over the nonempty set of
agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- Make-span of a vector of actual times `τ` (task `j` performed in time `τ j`) on the allocation
`x` (Def. 20): `g(x, τ) = maxₗ ∑_{j ∈ xˡ} τ_j`. -/
noncomputable def gT {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (τ : Fin k → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun l => ∑ j ∈ univ.filter (fun j => x j = l), τ j)

/-- The corrected time vector for agent `i` (Def. 22): agent `i`'s own tasks at their actual times
`tt`, every other task `j ∈ xˡ` (`l ≠ i`) at the time `dˡ_j` declared by its agent `l`. -/
def corr {n k : ℕ} (i : Fin n) (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) :
    Fin k → ℝ :=
  fun j => if x j = i then tt j else d (x j) j

/-- `corr*(x, d)` (Def. 22): every task `j ∈ xˡ` at the time `dˡ_j` declared by its agent. -/
def corrStar {n k : ℕ} (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) : Fin k → ℝ :=
  fun j => d (x j) j

/-- An execution plan of an agent: for every decision (allocation) `x`, the actual time in which
it performs task `j` (only its own tasks, `x j = i`, matter). Executions may depend on the
decision (Def. 18). -/
abbrev ExecPlan (n k : ℕ) := (Fin k → Fin n) → Fin k → ℝ

/-- An execution plan `e` is feasible for agent `i` of true type `ti` (Def. 20): every task
allocated to `i` is performed in at least its true time, `t̃_j ≥ tⁱ_j`. -/
def FeasibleExec {n k : ℕ} (i : Fin n) (ti : Fin k → ℝ) (e : ExecPlan n k) : Prop :=
  ∀ (x : Fin k → Fin n) (j : Fin k), x j = i → ti j ≤ e x j

/-- The actual times of the outcome when the declarations are `d` and the agents' execution plans
are `E`: task `j` is performed by its agent `alloc d j` according to that agent's plan, which
sees the decision `alloc d`. -/
def actualTimes {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) : Fin k → ℝ :=
  fun j => E (alloc d j) (alloc d) j

/-- Utility of agent `i` in the mechanism with verification `(alloc, pay)` (Def. 20): the
allocation `x = alloc d` depends on the declarations only, the payment `pay d t̃ i` (the amount
handed to agent `i`) on the declarations and the actual times, and the valuation is
`vⁱ(x, t̃) = -∑_{j ∈ xⁱ} t̃_j`. -/
def utility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ)
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n) : ℝ :=
  pay d (actualTimes alloc d E) i -
    ∑ j ∈ univ.filter (fun j => alloc d j = i), actualTimes alloc d E j

/-- The strategy `(di, ei)` is dominant for agent `i` of true type `ti` in the mechanism with
verification `(alloc, pay)` (Defs. 3, 18): `di` is a positive declaration, `ei` is feasible for
`ti`, and for all positive declarations of the others, all execution plans of the others, and
every alternative strategy `(di', ei')` with `di'` positive and `ei'` feasible for `ti`, the
utility of `(di, ei)` is at least that of `(di', ei')`. -/
def Dominant {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) (i : Fin n)
    (ti di : Fin k → ℝ) (ei : ExecPlan n k) : Prop :=
  IsAgentType di ∧ FeasibleExec i ti ei ∧
    ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ E : Fin n → ExecPlan n k,
      ∀ di' : Fin k → ℝ, IsAgentType di' → ∀ ei' : ExecPlan n k, FeasibleExec i ti ei' →
        utility alloc pay (Function.update d i di') (Function.update E i ei') i ≤
          utility alloc pay (Function.update d i di) (Function.update E i ei) i

/-- Truthfulness of a mechanism with verification (Def. 19): for every agent `i` and every
positive type `ti` there is an execution plan `ei` such that the strategy `(ti, ei)` (declare the
true type) is dominant. -/
def Truthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (ti : Fin k → ℝ), IsAgentType ti → ∃ ei : ExecPlan n k, Dominant alloc pay i ti ti ei

/-- Strong truthfulness of a mechanism with verification (Def. 19 and the proof of Theorem 5.1):
it is truthful, and every dominant strategy `(di, ei)` of an agent `i` of positive type `ti` is to
declare the true type, `di = ti`, and to perform every task allocated to `i` in minimal time,
`ei x j = tⁱ_j` whenever `x j = i`. -/
def StronglyTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  Truthful alloc pay ∧
    ∀ (i : Fin n) (ti : Fin k → ℝ), IsAgentType ti →
      ∀ (di : Fin k → ℝ) (ei : ExecPlan n k), Dominant alloc pay i ti di ei →
        di = ti ∧ ∀ (x : Fin k → Fin n) (j : Fin k), x j = i → ei x j = ti j

/-- `alloc` is an optimal allocation algorithm: on every positive declaration profile `d` its
allocation has the least make-span `g(·, d)` among all allocations. Ties are arbitrary. -/
def IsOptimalAlloc {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) :
    Prop :=
  ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ y : Fin k → Fin n, makespan d (alloc d) ≤ makespan d y

/-- The mechanism with verification `(alloc, pay)` implements the (exact) task scheduling problem
with dominant strategies (Def. 3, second bullet): for every positive true type vector `t` and every
profile of strategies `(D l, E l)` each dominant for its agent's true type, the output
`(x, t̃) = (alloc D, actual times)` has make-span `g(x, t̃)` at most the optimal make-span
`g(y, t)` of every allocation `y`. -/
def ImplementsOptimum {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ t : Fin n → Fin k → ℝ, IsType t →
    ∀ (D : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k),
      (∀ l : Fin n, Dominant alloc pay l (t l) (D l) (E l)) →
        ∀ y : Fin k → Fin n, gT (alloc D) (actualTimes alloc D E) ≤ makespan t y

/-- Participation constraints (Def. 28): for every positive declaration profile `t`, every vector
of actual times `t̃` and every agent `i`, if agent `i` performed each of its tasks
`j ∈ xⁱ(t)` in exactly its declared time `t̃_j = tⁱ_j`, then its utility
`pⁱ(t, t̃) + vⁱ(x(t), t̃)` is non-negative. -/
def Participation {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ (tt : Fin k → ℝ) (i : Fin n),
    (∀ j, alloc t j = i → tt j = t i j) →
      0 ≤ pay t tt i - ∑ j ∈ univ.filter (fun j => alloc t j = i), tt j

end AlgMechDesign.CompBonus
