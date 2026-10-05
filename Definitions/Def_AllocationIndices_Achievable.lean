import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_AllocationIndices_Superprocess

/-!
# Multi-armed Bandit Allocation Indices, Chapter 5: the achievable region methodology

Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices*, 2nd ed., Wiley 2011,
Chapter 5 (pp. 115–148): conservation laws, the achievable region and the adaptive greedy
algorithm.

**Generalized conservation laws (§5.4).** A *system* offers service to `N` job types
`E = {1, …, N}` (here `Fin N`). A scheduling policy `π` (an element of an abstract type `Pol`)
has a *performance* `xᵖ ∈ ℝ₊ᴺ`, an expectation; a permutation `σ` of `E` yields the *permutation
policy* `σ` which gives job type `σ_N` (here `σ (N-1)`) highest priority and `σ_1` (here `σ 0`)
lowest. The system satisfies **GCL(1)** (Definition 5.2, p. 125) if there are a set function
`b : 2^E → ℝ₊` and a matrix `A = (Aᵢ^S)` with `Aᵢ^S > 0` for `i ∈ S`, `Aᵢ^S = 0` for `i ∉ S`, such
that for every policy `∑_{i∈S} Aᵢ^S xᵢᵖ ≥ b(S)` (5.15) and `∑_{i∈E} Aᵢ^E xᵢᵖ = b(E)` (5.16), with
equality in (5.15) for every permutation policy whose `|S|` lowest-priority types are `S`.
**GCL(2)** (Definition 5.7, p. 128) is the same with the inequality reversed (matrix `F`, base
function `f`). The *achievable region* is `X = {xᵖ : π a policy}`.

**The adaptive greedy algorithm AG(A, r) (p. 122).** Working from the top, it picks `i_N`
maximizing `rᵢ / Aᵢ^E`, sets `ȳ_E` to that maximum and `S_{N-1} = E \ {i_N}`, then repeatedly
picks `i_{k-1} ∈ S_{k-1}` maximizing `(rᵢ − ∑_{j ≥ k} Aᵢ^{S_j} ȳ_{S_j}) / Aᵢ^{S_{k-1}}`, sets
`ȳ_{S_{k-1}}` to the maximum and `S_{k-2} = S_{k-1} \ {i_{k-1}}`. Its output is the priority
order `i_1, …, i_N` (encoded as the permutation `σ` with `σ (k-1) = i_k`), the dual variables
`ȳ_{S_k}` (encoded as `y (k-1)`) and the indices `ν_{i_k} = ∑_{j ≥ k} ȳ_{S_j}`.

**The SFABP as a GCL(1) system (§5.3, pp. 119–124).** `n` identical bandit processes on the
finite state space `E`, discount factor `a`, in the model of the *Bandit Algorithms* series
(`markovBanditMeasure`): the performance `xᵢᵖ = Eᵖ[∑_t aᵗ Iᵢ(t)]` is the discounted number of
times a bandit in state `i` is continued, `Aᵢ^S = E[1 + a + ⋯ + a^{Tᵢ^S − 1}]` (5.3) with `Tᵢ^S`
the number of steps for a bandit continued from `i ∈ S` to return to `S`, and `b(S)` is the
minimal cost `∑_{i∈S} Aᵢ^S xᵢᵖ`, attained by any policy giving priority to bandits whose states
are not in `S` (Lemma 5.1, p. 120).
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

/-! ### Generalized conservation laws -/

section GCL

variable {N : ℕ}

/-- `lowSet σ k`: the `k` lowest-priority job types under the permutation policy `σ`, the book's
`S_k = {σ_1, …, σ_k}` (p. 122; `σ 0` has lowest priority, `σ (N-1)` highest). -/
def lowSet (σ : Equiv.Perm (Fin N)) (k : ℕ) : Finset (Fin N) :=
  (univ.filter fun j : Fin N ↦ (j : ℕ) < k).image σ

/-- A system satisfying the **generalized conservation laws of type 1**, GCL(1) (Definition 5.2,
p. 125): policies of type `Pol`, a nonnegative performance `perf π ∈ ℝ₊ᴺ` for each policy, a
permutation policy for each priority order, a base function `b ≥ 0` and a matrix `A` positive
on `S` and zero off it, with `∑_{i∈S} Aᵢ^S xᵢᵖ ≥ b(S)` for every policy and every `S`,
`∑_{i∈E} Aᵢ^E xᵢᵖ = b(E)`, and equality for the permutation policies whose `|S|` lowest-priority
types are exactly `S`. -/
structure GCL1System (N : ℕ) (Pol : Type*) where
  /-- The performance `xᵖ` of policy `π`, an `N`-vector of expectations. -/
  perf : Pol → Fin N → ℝ
  /-- Performances are nonnegative. -/
  perf_nonneg : ∀ π i, 0 ≤ perf π i
  /-- The base function `b : 2^E → ℝ₊`. -/
  b : Finset (Fin N) → ℝ
  /-- `b ≥ 0`. -/
  b_nonneg : ∀ S, 0 ≤ b S
  /-- The matrix `A = (Aᵢ^S)`, indexed by `S ⊆ E` and `i ∈ E`. -/
  A : Finset (Fin N) → Fin N → ℝ
  /-- `Aᵢ^S > 0` for `i ∈ S`. -/
  A_pos : ∀ S i, i ∈ S → 0 < A S i
  /-- `Aᵢ^S = 0` for `i ∉ S`. -/
  A_eq_zero : ∀ S i, i ∉ S → A S i = 0
  /-- The permutation policy of the priority order `σ` (`σ (N-1)` first, `σ 0` last). -/
  permPolicy : Equiv.Perm (Fin N) → Pol
  /-- (5.15): `∑_{i∈S} Aᵢ^S xᵢᵖ ≥ b(S)` for every policy and every `S`. -/
  law_ge : ∀ π S, b S ≤ ∑ i ∈ S, A S i * perf π i
  /-- (5.16): `∑_{i∈E} Aᵢ^E xᵢᵖ = b(E)` for every policy. -/
  law_univ : ∀ π, ∑ i, A univ i * perf π i = b univ
  /-- Equality in (5.15) for every permutation policy whose `|S|` lowest-priority types are `S`. -/
  law_perm : ∀ (σ : Equiv.Perm (Fin N)) S, lowSet σ S.card = S →
    ∑ i ∈ S, A S i * perf (permPolicy σ) i = b S

/-- A system satisfying the **generalized conservation laws of type 2**, GCL(2) (Definition 5.7,
pp. 128–129): as `GCL1System` with the inequality (5.15) reversed, `∑_{i∈S} Fᵢ^S xᵢᵖ ≤ f(S)`
(5.18), equality `∑_{i∈E} Fᵢ^E xᵢᵖ = f(E)` (5.19), and equality in (5.18) for the permutation
policies whose `|S|` lowest-priority types are `S`. -/
structure GCL2System (N : ℕ) (Pol : Type*) where
  /-- The performance `xᵖ` of policy `π`. -/
  perf : Pol → Fin N → ℝ
  /-- Performances are nonnegative. -/
  perf_nonneg : ∀ π i, 0 ≤ perf π i
  /-- The base function `f : 2^E → ℝ₊`. -/
  f : Finset (Fin N) → ℝ
  /-- `f ≥ 0`. -/
  f_nonneg : ∀ S, 0 ≤ f S
  /-- The matrix `F = (Fᵢ^S)`. -/
  F : Finset (Fin N) → Fin N → ℝ
  /-- `Fᵢ^S > 0` for `i ∈ S`. -/
  F_pos : ∀ S i, i ∈ S → 0 < F S i
  /-- `Fᵢ^S = 0` for `i ∉ S`. -/
  F_eq_zero : ∀ S i, i ∉ S → F S i = 0
  /-- The permutation policy of the priority order `σ`. -/
  permPolicy : Equiv.Perm (Fin N) → Pol
  /-- (5.18): `∑_{i∈S} Fᵢ^S xᵢᵖ ≤ f(S)` for every policy and every `S`. -/
  law_le : ∀ π S, ∑ i ∈ S, F S i * perf π i ≤ f S
  /-- (5.19): `∑_{i∈E} Fᵢ^E xᵢᵖ = f(E)` for every policy. -/
  law_univ : ∀ π, ∑ i, F univ i * perf π i = f univ
  /-- Equality in (5.18) for every permutation policy whose `|S|` lowest-priority types are `S`. -/
  law_perm : ∀ (σ : Equiv.Perm (Fin N)) S, lowSet σ S.card = S →
    ∑ i ∈ S, F S i * perf (permPolicy σ) i = f S

/-- The polytope `P(A, b)` of Theorem 5.5 (p. 127):
`{x ∈ ℝ₊ᴺ : ∑_{i∈S} Aᵢ^S xᵢ ≥ b(S) for S ⊂ E, ∑_{i∈E} Aᵢ^E xᵢ = b(E)}`. -/
def achievablePolytope (A : Finset (Fin N) → Fin N → ℝ) (b : Finset (Fin N) → ℝ) :
    Set (Fin N → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∀ S, S ≠ univ → b S ≤ ∑ i ∈ S, A S i * x i) ∧
    ∑ i, A univ i * x i = b univ}

/-- The polytope `P'(F, f)` of Theorem 5.10 (p. 130):
`{x ∈ ℝ₊ᴺ : ∑_{i∈S} Fᵢ^S xᵢ ≤ f(S) for S ⊂ E, ∑_{i∈E} Fᵢ^E xᵢ = f(E)}`. -/
def achievablePolytope' (F : Finset (Fin N) → Fin N → ℝ) (f : Finset (Fin N) → ℝ) :
    Set (Fin N → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∀ S, S ≠ univ → ∑ i ∈ S, F S i * x i ≤ f S) ∧
    ∑ i, F univ i * x i = f univ}

/-- A linear objective `∑_{i∈E} rᵢ xᵢ` in the performance `x` (`R^π = ∑ rᵢ xᵢᵖ`, p. 127;
`C^π = ∑ cᵢ xᵢᵖ`, p. 130). -/
def linearObjective (r x : Fin N → ℝ) : ℝ :=
  ∑ i, r i * x i

/-- The numerator `rᵢ − ∑_{j > k} Aᵢ^{S_{j+1}} ȳ_{S_{j+1}}` of the ratio maximized at stage `k` of
the adaptive greedy algorithm (p. 122), where `S_{j+1} = lowSet σ (j+1)` and `y j = ȳ_{S_{j+1}}`
(the stages already completed are those with `j > k`). -/
def greedyNumerator (A : Finset (Fin N) → Fin N → ℝ) (r : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (y : Fin N → ℝ) (k i : Fin N) : ℝ :=
  r i - ∑ j ∈ univ.filter (fun j : Fin N ↦ k < j), A (lowSet σ ((j : ℕ) + 1)) i * y j

/-- `IsAdaptiveGreedy A r σ y`: the priority order `σ` (`σ k = i_{k+1}`) and the dual variables
`y` (`y k = ȳ_{S_{k+1}}`) are an output of the adaptive greedy algorithm `AG(A, r)` (p. 122): at
every stage `k` (from `N − 1` down to `0`), `y k` is the maximum over `i ∈ S_{k+1}` of
`(rᵢ − ∑_{j>k} Aᵢ^{S_{j+1}} y j) / Aᵢ^{S_{k+1}}` and `σ k` attains it. Ties may be broken
arbitrarily. -/
def IsAdaptiveGreedy (A : Finset (Fin N) → Fin N → ℝ) (r : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (y : Fin N → ℝ) : Prop :=
  ∀ k : Fin N,
    (∀ i ∈ lowSet σ ((k : ℕ) + 1),
      greedyNumerator A r σ y k i / A (lowSet σ ((k : ℕ) + 1)) i ≤ y k) ∧
    greedyNumerator A r σ y k (σ k) / A (lowSet σ ((k : ℕ) + 1)) (σ k) = y k

/-- The indices `ν_{i_k} = ȳ_{S_N} + ȳ_{S_{N-1}} + ⋯ + ȳ_{S_k}` computed by the adaptive greedy
algorithm (p. 122): `greedyIndex σ y i = ∑_{j ≥ σ⁻¹ i} y j`. -/
def greedyIndex (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin N ↦ σ.symm i ≤ j), y j

end GCL

/-! ### The SFABP with identical arms as a GCL(1) system (§5.3) -/

section SFABP

variable {N n : ℕ}

/-- `Aᵢ^S = E[1 + a + ⋯ + a^{Tᵢ^S − 1}]`, Eq. (5.3) (p. 120): the expected discounted number of
steps for a bandit continued from state `i ∈ S` to return to `S` (`Tᵢ^S` is the first time
`t ≥ 1` at which the chain from `i` is in `S`, `∞` if never, when the sum is `1/(1−a)`); `0` for
`i ∉ S`. `Aᵢ^E = 1`. -/
noncomputable def conservationCoeff (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (S : Finset (Fin N)) (i : Fin N) : ℝ :=
  if i ∈ S then stoppedTime P a (hittingTime (↑S : Set (Fin N))) i else 0

/-- `b(S)`, the minimal value of `∑_{i∈S} Aᵢ^S xᵢᵖ` from the initial state-vector `k` (p. 120):
`(1 − a)⁻¹ E[a^{τ}]` where `τ = ∑_{j : k_j ∉ S} T_{k_j}^S` is the total number of continuations
needed to bring every bandit into `S`; by independence of the bandits this is
`(1 − a)⁻¹ ∏_{j : k_j ∉ S} E[a^{T_{k_j}^S}]` (`a^∞ = 0`). (The book prints this product as a
sum, `(1 − a)⁻¹ ∑_{i : k_i ∉ S} E[a^{T_{k_i}^S}]`, which gives `0` instead of `1/(1−a)` when
every bandit starts in `S` and is not the minimal cost when two or more start outside; the
product is what the argument of p. 120 establishes.) `b(E) = 1/(1−a)`. -/
noncomputable def conservationBase (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (k : Fin n → Fin N) (S : Finset (Fin N)) : ℝ :=
  (1 - a)⁻¹ * ∏ j ∈ univ.filter (fun j ↦ k j ∉ S),
    discountAtStop P a (hittingTime (↑S : Set (Fin N))) (k j)

/-- `Pᵖ[the bandit continued in round t is in state i]` (round `t` is 0-indexed), in the
*Bandit Algorithms* model of the SFABP with `n` identical bandits on `E` and initial
state-vector `k`. -/
noncomputable def roundOccupation (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P]
    (π : MarkovBanditPolicy n (Fin N)) (k : Fin n → Fin N) (i : Fin N) (t : ℕ) : ℝ :=
  (markovBanditMeasure P π k (t + 1)
    {h | (h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2) = i}).toReal

/-- The performance `xᵢᵖ = Eᵖ[∑_{t≥0} aᵗ Iᵢ(t) | k]`, Eq. (5.1) (p. 119): the total discounted
number of times a bandit in state `i` is continued under `π` from the initial state-vector `k`. -/
noncomputable def performance (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P]
    (π : MarkovBanditPolicy n (Fin N)) (a : ℝ) (k : Fin n → Fin N) (i : Fin N) : ℝ :=
  ∑' t : ℕ, a ^ t * roundOccupation P π k i t

/-- `GivesPriority S π`: the policy gives priority to bandits whose states are not in `S` over
any bandits whose states are in `S` (Lemma 5.1, p. 120): whenever some bandit is in a state
outside `S`, the bandit continued is almost surely one of those. -/
def GivesPriority (S : Finset (Fin N)) (π : MarkovBanditPolicy n (Fin N)) : Prop :=
  ∀ t (h : MarkovBanditHistory n (Fin N) t), (∃ j, h.2 j ∉ S) →
    (π.select t) h {j | h.2 j ∉ S} = 1

end SFABP

end AllocationIndices
