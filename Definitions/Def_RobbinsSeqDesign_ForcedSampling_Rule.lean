import Mathlib
import Definitions.Def_BanditPolicy

namespace RobbinsSeqDesign.ForcedSampling

open MeasureTheory ProbabilityTheory Filter Topology BanditAlgorithm

open Classical in
/-- Robbins (1952), Section 2, Eq. (13), p. 532: two fixed, disjoint, strictly increasing
sequences of positive integers `1 = a₁ < a₂ < ⋯` and `2 = b₁ < b₂ < ⋯` of density `0`:
the proportion of the integers `1, 2, …, n` that are either an `a` or a `b` tends to `0`.
The paper's `a_{j+1}` is `a j` here (0-based index), so `a 0 = 1` and `b 0 = 2`. -/
structure ForcedSchedule where
  /-- The sequence `a₁ < a₂ < ⋯` (`a j` is the paper's `a_{j+1}`). -/
  a : ℕ → ℕ
  /-- The sequence `b₁ < b₂ < ⋯` (`b j` is the paper's `b_{j+1}`). -/
  b : ℕ → ℕ
  a_strictMono : StrictMono a
  b_strictMono : StrictMono b
  /-- `a₁ = 1`. -/
  a_zero : a 0 = 1
  /-- `b₁ = 2`. -/
  b_zero : b 0 = 2
  /-- The two sequences are disjoint. -/
  disjoint : Disjoint (Set.range a) (Set.range b)
  /-- Density `0`: `#{i ∈ {1, …, n} : i is an a or a b} / n → 0`. -/
  density_zero :
    Tendsto (fun n : ℕ =>
      (((Finset.Icc 1 n).filter (fun i => i ∈ Set.range a ∪ Set.range b)).card : ℝ) / (n : ℝ))
      atTop (𝓝 0)

open Classical in
/-- The population (`0` = A, `1` = B) from which the rule `R̄` takes draw number `n + 1`,
given the history `h` of the first `n` draws (Robbins 1952, p. 532): A if `n + 1` is an `a`,
B if `n + 1` is a `b`, and otherwise A if the arithmetic mean of the previous observations
from A exceeds that of the previous observations from B, and B if it does not exceed it
(a tie goes to B). -/
noncomputable def ruleChoice (σ : ForcedSchedule) (n : ℕ) (h : BanditHistory 2 n) : Fin 2 :=
  if n + 1 ∈ Set.range σ.a then 0
  else if n + 1 ∈ Set.range σ.b then 1
  else if armEmpiricalMean 1 h < armEmpiricalMean 0 h then 0 else 1

/-- The empirical mean of an arm is a measurable function of the history (structural). -/
lemma measurable_armEmpiricalMean {n : ℕ} (i : Fin 2) :
    Measurable (fun h : BanditHistory 2 n => armEmpiricalMean i h) := by
  classical
  have hset : ∀ t : Fin n, MeasurableSet {h : BanditHistory 2 n | (h t).1 = i} := fun t =>
    (measurable_fst.comp (measurable_pi_apply t)) (measurableSet_singleton i)
  have heq : (fun h : BanditHistory 2 n => armEmpiricalMean i h) = fun h =>
      (∑ t : Fin n, if (h t).1 = i then (h t).2 else 0) /
        ((∑ t : Fin n, if (h t).1 = i then (1 : ℕ) else 0 : ℕ) : ℝ) := by
    funext h
    simp only [armEmpiricalMean, armPullCount, Set.toFinset_ofPred, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  rw [heq]
  refine Measurable.div ?_ ?_
  · refine Finset.measurable_sum _ fun t _ => ?_
    exact Measurable.ite (hset t) (measurable_snd.comp (measurable_pi_apply t)) measurable_const
  · refine measurable_from_top.comp ?_
    refine Finset.measurable_sum _ fun t _ => ?_
    exact Measurable.ite (hset t) measurable_const measurable_const

/-- The choice map of `R̄` is measurable (structural, needed for the kernel). -/
lemma measurable_ruleChoice (σ : ForcedSchedule) (n : ℕ) :
    Measurable (ruleChoice σ n) := by
  classical
  unfold ruleChoice
  refine Measurable.ite (MeasurableSet.const _) measurable_const ?_
  refine Measurable.ite (MeasurableSet.const _) measurable_const ?_
  exact Measurable.ite (measurableSet_lt (measurable_armEmpiricalMean 1)
    (measurable_armEmpiricalMean 0)) measurable_const measurable_const

/-- Robbins' sampling rule `R̄` (Section 2, p. 532) as a deterministic bandit policy on the two
populations A = arm `0` and B = arm `1`: the kernel for draw `n + 1` is the Dirac mass at
`ruleChoice σ n h`. -/
noncomputable def rule (σ : ForcedSchedule) : BanditPolicy 2 where
  select n := ProbabilityTheory.Kernel.deterministic (ruleChoice σ n) (measurable_ruleChoice σ n)
  markov _ := inferInstance

end RobbinsSeqDesign.ForcedSampling
