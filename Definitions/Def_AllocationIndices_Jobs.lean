import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_AllocationIndices_Index

/-!
Gittins, Glazebrook and Weber, *Multi-armed Bandit Allocation Indices* (2nd ed., Wiley 2011),
Chapter 3 (pp. 55-78): necessary assumptions for indices; jobs, search, multiple processors.

Three self-contained models of the chapter's proved results.

**Deterministic jobs on parallel machines (§3.4.3, §3.5.5).** `n` jobs with service times `s_i`
(and weights `c_i`) are processed by `m` identical machines; a `Schedule` assigns each job a
machine and a position in that machine's processing order, and machines process their jobs
consecutively without idling. `completionTime` is `C_i`, `flowTime = ∑_i C_i`,
`weightedFlowTime = ∑_i c_i C_i`, `load` is the total process time of a machine and
`loadDeviation` its excess over the average `S/m` (Theorem 3.3's `δ_j`); `levelFromEnd` is the
position of a job counted from the end of its machine's schedule; `rankDesc` is the rank of a job
by decreasing service time; `sptSchedule` is the list schedule that orders the jobs by increasing
service time and deals them out cyclically to the machines (Theorem 3.7).

**The discrete search problem (§3.5.4, Problem 3).** A stationary object is hidden in one of `n`
boxes, in box `i` with probability `p_i`; a search of box `i` costs `c_i` and finds the object with
probability `q_i` if it is there. A (deterministic) search policy is a sequence of boxes;
`searchCount σ k i` is the number of searches of box `i` among the first `k`; the object has not
been found after the first `k` searches with probability `∑_i p_i (1 − q_i)^{N_i(k)}`, so the
expected cost is `searchCost σ = ∑_k c_{σ_k} ∑_i p_i (1 − q_i)^{N_i(k)}`, in `ℝ≥0∞` (a policy that
neglects a box has infinite cost). After `N_i` unsuccessful searches the posterior probability
that the object is in box `i` is proportional to `p_i (1 − q_i)^{N_i}` (Bayes' theorem), and the
index of Theorem 3.6 is `p'_i q_i / c_i`; `ConformsToSearchIndex σ` says every search is of a box
of maximal index at that time, and `IsOptimalSearch σ` that no policy has smaller expected cost.

**Two bandit processes with different discount factors (§3.5.1, Theorem 3.4).** Bandit `A` on
`S_A` (kernel `P_A`, reward `r_A`, discount `a`) and bandit `B` on `S_B` (`P_B`, `r_B`, `b`) form a
simple family of two alternative bandit processes on the disjoint union `S_A ⊕ S_B`, in the
Bandit Algorithms model (`MarkovBanditPolicy 2 (S_A ⊕ S_B)`, `markovBanditMeasure`), a reward
obtained at time `t` from `A` being discounted by `a^t` and from `B` by `b^t`:
`twoDiscountValue`. The indices of Theorem 3.4, in the form its proof yields, are
`νAB(x) = sup_{τ>0} R_τ(A; a) / E[1 − b^τ]` and `νBA(y) = sup_{τ>0} R_τ(B; b) / E[1 − a^τ]`, each
computed from one process's stopping times but with the other's discount factor in the
denominator (`crossIndex`); `IsTwoDiscountIndexPolicy` selects, in round `t`, `A` when
`a^t νAB(x) > b^t νBA(y)` and `B` when `a^t νAB(x) < b^t νBA(y)`. Both differ from the printed
statement, which is false; see the docstrings below.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

noncomputable section

namespace AllocationIndices

/-! ### Deterministic jobs on parallel machines -/

/-- A schedule of `n` jobs on `m` identical machines: each job is assigned a machine and a
position in that machine's processing order, two jobs on the same machine having different
positions. Machines process their jobs consecutively, without idling. -/
structure Schedule (n m : ℕ) where
  /-- The machine that processes job `i`. -/
  machine : Fin n → Fin m
  /-- The position of job `i` in its machine's processing order. -/
  pos : Fin n → ℕ
  pos_inj : ∀ i j, machine i = machine j → pos i = pos j → i = j

variable {n m : ℕ}

/-- The completion time `C_i` of job `i`: the total service time of the jobs processed on its
machine up to and including itself. -/
def completionTime (σ : Schedule n m) (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n with σ.machine j = σ.machine i ∧ σ.pos j ≤ σ.pos i, s j

/-- The flow time `∑_i C_i` of a schedule (p. 58). -/
def flowTime (σ : Schedule n m) (s : Fin n → ℝ) : ℝ :=
  ∑ i, completionTime σ s i

/-- The weighted flow time `∑_i c_i C_i` with weights `c_i` (p. 58). -/
def weightedFlowTime (σ : Schedule n m) (s c : Fin n → ℝ) : ℝ :=
  ∑ i, c i * completionTime σ s i

/-- The total process time (load) of machine `j`. -/
def load (σ : Schedule n m) (s : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i : Fin n with σ.machine i = j, s i

/-- Theorem 3.3's `δ_j`: the excess of the load of machine `j` over the average `S/m`,
`S = ∑_i s_i`. -/
def loadDeviation (σ : Schedule n m) (s : Fin n → ℝ) (j : Fin m) : ℝ :=
  load σ s j - (∑ i, s i) / m

/-- The position of job `i` counted from the end of its machine's schedule (`1` for the last
job processed on that machine). -/
def levelFromEnd (σ : Schedule n m) (i : Fin n) : ℕ :=
  #{j : Fin n | σ.machine j = σ.machine i ∧ σ.pos i ≤ σ.pos j}

/-- The rank of job `i` by decreasing service time, `1` for a longest job:
`1 + #{j : s_j > s_i}`. -/
def rankDesc (s : Fin n → ℝ) (i : Fin n) : ℕ :=
  1 + #{j : Fin n | s i < s j}

/-- The number of jobs shorter than job `i`, ties broken by index: the position of `i` in the
increasing order of service times. -/
def rankAsc (s : Fin n → ℝ) (i : Fin n) : ℕ :=
  #{j : Fin n | s j < s i ∨ (s j = s i ∧ j < i)}

/-- The SPT list schedule (Theorem 3.7): the jobs in order of increasing service time are dealt
out cyclically to the machines, the `k`-th shortest job going to machine `k mod m` in position
`k / m`, for `m ≥ 1`. -/
def sptSchedule (s : Fin n → ℝ) (hm : 0 < m) : Schedule n m where
  machine i := ⟨rankAsc s i % m, Nat.mod_lt _ hm⟩
  pos i := rankAsc s i / m
  pos_inj i j hmach hpos := by
    have h : rankAsc s i = rankAsc s j := by
      have h1 : rankAsc s i % m = rankAsc s j % m := congrArg Fin.val hmach
      rw [← Nat.div_add_mod (rankAsc s i) m, ← Nat.div_add_mod (rankAsc s j) m, hpos, h1]
    by_contra hij
    have hlt : i < j ∨ j < i := lt_or_gt_of_ne hij
    have key : ∀ i j : Fin n, i < j → rankAsc s i ≠ rankAsc s j := by
      intro i j hij
      unfold rankAsc
      rcases lt_trichotomy (s i) (s j) with h | h | h
      · -- every job counted for `i` is counted for `j`, and `i` itself is counted for `j` only
        exact ne_of_lt (Finset.card_lt_card (Finset.ssubset_iff_of_subset
          (fun k hk ↦ by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
            rcases hk with hk | ⟨hk1, hk2⟩
            · exact Or.inl (lt_trans hk h)
            · exact Or.inl (hk1 ▸ h)) |>.2
          ⟨i, by simp [h], by simp⟩))
      · exact ne_of_lt (Finset.card_lt_card (Finset.ssubset_iff_of_subset
          (fun k hk ↦ by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
            rcases hk with hk | ⟨hk1, hk2⟩
            · exact Or.inl (h ▸ hk)
            · exact Or.inr ⟨hk1.trans h, lt_trans hk2 hij⟩) |>.2
          ⟨i, by simp [h, hij], by simp⟩))
      · exact ne_of_gt (Finset.card_lt_card (Finset.ssubset_iff_of_subset
          (fun k hk ↦ by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
            rcases hk with hk | ⟨hk1, hk2⟩
            · exact Or.inl (lt_trans hk h)
            · exact Or.inl (hk1 ▸ h)) |>.2
          ⟨j, by simp [h], by simp⟩))
    rcases hlt with hlt | hlt
    · exact key i j hlt h
    · exact key j i hlt h.symm

/-! ### The discrete search problem -/

/-- The number of searches of box `i` among the first `k` searches of the policy `σ`. -/
def searchCount (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) : ℕ :=
  #{t : Fin k | σ t = i}

/-- The probability that the object has not been found by the first `k` searches:
`∑_i p_i (1 − q_i)^{N_i(k)}`. -/
def notFoundProb (p q : Fin n → ℝ) (σ : ℕ → Fin n) (k : ℕ) : ℝ :=
  ∑ i, p i * (1 - q i) ^ searchCount σ k i

/-- The expected cost of finding the object under the search policy `σ` (Problem 3, p. 70):
`∑_k c_{σ_k} · Pr[not found before search k+1]`, in `ℝ≥0∞`. -/
def searchCost (p q c : Fin n → ℝ) (σ : ℕ → Fin n) : ENNReal :=
  ∑' k : ℕ, ENNReal.ofReal (c (σ k) * notFoundProb p q σ k)

/-- The (unnormalized) search index of box `i` after the first `k` searches: the posterior
probability that the object is in box `i` is proportional to `p_i (1 − q_i)^{N_i(k)}`, and the
index of Theorem 3.6 is `p'_i q_i / c_i`, so up to the common normalizing constant it is
`p_i (1 − q_i)^{N_i(k)} q_i / c_i`. -/
def searchIndex (p q c : Fin n → ℝ) (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) : ℝ :=
  p i * (1 - q i) ^ searchCount σ k i * q i / c i

/-- The policy conforms to the index `p'_i q_i / c_i` (Theorem 3.6): at every step it searches a
box of maximal current index. -/
def ConformsToSearchIndex (p q c : Fin n → ℝ) (σ : ℕ → Fin n) : Prop :=
  ∀ k i, searchIndex p q c σ k i ≤ searchIndex p q c σ k (σ k)

/-- An optimal search policy: no policy has smaller expected cost. -/
def IsOptimalSearch (p q c : Fin n → ℝ) (σ : ℕ → Fin n) : Prop :=
  ∀ σ' : ℕ → Fin n, searchCost p q c σ ≤ searchCost p q c σ'

/-! ### Two bandit processes with bandit-dependent discount factors -/

section TwoDiscount

variable {SA SB : Type*} [MeasurableSpace SA] [MeasurableSpace SB]

/-- The transition kernel of the simple family `{A, B}` on the disjoint union `S_A ⊕ S_B`: a
state of `A` moves by `P_A`, a state of `B` by `P_B`. -/
def sumKernel (PA : Kernel SA SA) (PB : Kernel SB SB) : Kernel (SA ⊕ SB) (SA ⊕ SB) where
  toFun := Sum.elim (fun x ↦ (PA.map Sum.inl) x) (fun y ↦ (PB.map Sum.inr) y)
  measurable' := (PA.map Sum.inl).measurable.sumElim (PB.map Sum.inr).measurable

instance sumKernel.instIsMarkovKernel (PA : Kernel SA SA) [IsMarkovKernel PA]
    (PB : Kernel SB SB) [IsMarkovKernel PB] : IsMarkovKernel (sumKernel PA PB) := by
  constructor
  rintro (x | y)
  · exact (Kernel.IsMarkovKernel.map PA measurable_inl).isProbabilityMeasure x
  · exact (Kernel.IsMarkovKernel.map PB measurable_inr).isProbabilityMeasure y

/-- The reward on the disjoint union: `r_A` on states of `A`, `r_B` on states of `B`. -/
def sumReward (rA : SA → ℝ) (rB : SB → ℝ) : SA ⊕ SB → ℝ :=
  Sum.elim rA rB

/-- The initial state-vector of the family: `A` in state `x`, `B` in state `y`. -/
def twoStates (x : SA) (y : SB) : Fin 2 → SA ⊕ SB :=
  ![Sum.inl x, Sum.inr y]

/-- The expected reward collected in round `t` (0-indexed) from arm `k` under policy `π`:
`E[r(S_{A_t}) 𝟙{A_t = k}]` over the horizon-`(t+1)` law of the Bandit Algorithms model. -/
def armRoundReward (PA : Kernel SA SA) [IsMarkovKernel PA] (PB : Kernel SB SB) [IsMarkovKernel PB]
    (rA : SA → ℝ) (rB : SB → ℝ) (π : MarkovBanditPolicy 2 (SA ⊕ SB)) (x : SA) (y : SB)
    (k : Fin 2) (t : ℕ) : ℝ :=
  ∫ h, (if (h.1 (Fin.last t)).2 = k then
      sumReward rA rB ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)) else 0)
    ∂markovBanditMeasure (sumKernel PA PB) π (twoStates x y) (t + 1)

/-- The payoff of the two-bandit family with bandit-dependent discount factors (§3.5.1): a
reward obtained at time `t` from `A` is discounted by `a^t` and one from `B` by `b^t`,
`∑_t (a^t E[r_A 𝟙{A_t = A}] + b^t E[r_B 𝟙{A_t = B}])`. -/
def twoDiscountValue (PA : Kernel SA SA) [IsMarkovKernel PA] (PB : Kernel SB SB)
    [IsMarkovKernel PB] (rA : SA → ℝ) (rB : SB → ℝ) (a b : ℝ)
    (π : MarkovBanditPolicy 2 (SA ⊕ SB)) (x : SA) (y : SB) : ℝ :=
  ∑' t : ℕ, (a ^ t * armRoundReward PA PB rA rB π x y 0 t +
    b ^ t * armRoundReward PA PB rA rB π x y 1 t)

/-- The index `ν_{AB}(x) = sup_{τ>0} E[∑_{t<τ} a^t r_A(x(t))] / E[1 − b^τ]` of Theorem 3.4: the
supremum over positive stopping times of `A` of `A`'s `a`-discounted reward divided by
`E[1 − b^τ] = (1 − b) E[∑_{t<τ} b^t]` (and `ν_{BA}` with the roles exchanged).

The book prints the denominator as `E ∫_0^τ b^t dt = E[1 − b^τ] / ln(1/b)`. Its own proof (the
change of time scale to a common discount factor `c`) gives `E[1 − b^τ] / ln(1/c)` for `A` and
`E[1 − a^τ] / ln(1/c)` for `B`, and so does Nash's generalized-bandit form on p. 66. The factor
`ln(1/c)` is common to both processes, while the printed `ln(1/b)` and `ln(1/a)` are not, so the
printed indices compare the processes wrongly when `a ≠ b`. -/
def crossIndex {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ)
    (a b : ℝ) (x : S) : ℝ :=
  ⨆ τ : {τ : (ℕ → S) → ℕ∞ // IsPositiveStoppingTime τ},
    stoppedReward P r a τ x / ((1 - b) * stoppedTime P b τ x)

/-- The policy of Theorem 3.4, corrected: in round `t` (0-indexed; the global time), with `A` in
state `x` and `B` in state `y`, it selects `A` if `a^t ν_{AB}(x) > b^t ν_{BA}(y)` and `B` if
`a^t ν_{AB}(x) < b^t ν_{BA}(y)` (almost surely in the selection kernel); with equality either
choice is allowed. The factors `a^t` and `b^t` are the discounts already accrued by each process's
future rewards. Without them the rule is stationary in the states, and no stationary rule is
optimal in general: two one-state bandits paying `0.18` (`a = 0.9`) and `1` (`b = 0.5`) are best
served by `B` for three rounds and then `A` forever (payoff `3.062`), not by either one forever. -/
def IsTwoDiscountIndexPolicy (PA : Kernel SA SA) [IsMarkovKernel PA] (PB : Kernel SB SB)
    [IsMarkovKernel PB] (rA : SA → ℝ) (rB : SB → ℝ) (a b : ℝ)
    (π : MarkovBanditPolicy 2 (SA ⊕ SB)) : Prop :=
  ∀ t (h : MarkovBanditHistory 2 (SA ⊕ SB) t) (x : SA) (y : SB),
    h.2 0 = Sum.inl x → h.2 1 = Sum.inr y →
      (b ^ t * crossIndex PB rB b a y < a ^ t * crossIndex PA rA a b x →
        (π.select t) h {0} = 1) ∧
      (a ^ t * crossIndex PA rA a b x < b ^ t * crossIndex PB rB b a y →
        (π.select t) h {1} = 1)

end TwoDiscount

end AllocationIndices

end
