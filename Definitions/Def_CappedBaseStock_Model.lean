import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.ENNReal
import Mathlib.Tactic

/-!
# Periodic-review lost-sales model for the capped base-stock approximation theorem

This file contains definitions, with no admitted facts. Time is zero-based: `t = 0`
is period 1 of the manuscript. The state is immediately before delivery, so an order
placed at `t` first arrives at `t + L`. Both initial inventory and pipeline are zero.

The probability space is the canonical i.i.d. nonnegative demand path together with
an independent uniform `[0,1]` seed. An admissible policy is an arbitrary sequence of
Borel measurable functions of the strict demand history and that private seed. Thus
policies need not be stationary, Markov, bounded, or integrable. This is the standard
Borel realization convention for randomized nonanticipative policies; deterministic
policies simply ignore the seed. Equivalence with formulations on arbitrary private
probability spaces is not proved here. Past orders and states are functions of the same
history and seed. Costs and both policy infima take values in `ℝ≥0∞`, so divergent
expectations and infinite long-run costs are retained as infinity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace CappedBaseStock

/-- Exactly the paper's distribution assumptions: nonnegative demand, probability
law, finite mean, and strictly positive mean. -/
structure DemandLaw where
  law : Measure ℝ≥0
  probability : IsProbabilityMeasure law
  finiteMean : Integrable (fun d : ℝ≥0 => (d : ℝ)) law
  positiveMean : 0 < ∫ d : ℝ≥0, (d : ℝ) ∂law

attribute [instance] DemandLaw.probability

/-- The (finite real) mean demand. -/
def mean (P : DemandLaw) : ℝ := ∫ d : ℝ≥0, (d : ℝ) ∂P.law

/-- Exactly the lead-time and cost assumptions in the model. -/
structure Parameters where
  L : ℕ
  leadTime_pos : 1 ≤ L
  h : ℝ
  p : ℝ
  holding_pos : 0 < h
  penalty_pos : 0 < p

abbrev DemandPath := ℕ → ℝ≥0
abbrev Sample := DemandPath × ℝ

/-- Canonical i.i.d. demand measure. -/
def demandPathLaw (P : DemandLaw) : Measure DemandPath :=
  Measure.infinitePi (fun _ : ℕ => P.law)

/-- Private uniform seed in the chosen realization of randomized history-dependent
control rules. The whole seed is available to the controller before period 0. -/
def seedLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance seedLaw_probability : IsProbabilityMeasure seedLaw := by
  constructor
  simp [seedLaw, Real.volume_Icc]

/-- Independent product of the complete demand sequence and the private seed. -/
def sampleLaw (P : DemandLaw) : Measure Sample := (demandPathLaw P).prod seedLaw

instance demandPathLaw_probability (P : DemandLaw) : IsProbabilityMeasure (demandPathLaw P) := by
  unfold demandPathLaw
  infer_instance

instance sampleLaw_probability (P : DemandLaw) : IsProbabilityMeasure (sampleLaw P) := by
  unfold sampleLaw
  infer_instance

/-- The demand observations that are available before the order at time `t`. -/
def history (t : ℕ) (ω : Sample) : (Fin t → ℝ≥0) × ℝ :=
  (fun i => ω.1 i, ω.2)

/-- The full class of measurable nonanticipative policies, allowing time dependence
and private randomization. Current demand `D_t` is absent from the arguments. -/
structure AdmissiblePolicy where
  decision : (t : ℕ) → ((Fin t → ℝ≥0) × ℝ) → ℝ≥0
  measurable_decision : ∀ t, Measurable (decision t)

/-- The order induced on the canonical probability space. -/
def order (π : AdmissiblePolicy) (t : ℕ) (ω : Sample) : ℝ≥0 :=
  π.decision t (history t ω)

/-- Pre-delivery on-hand inventory and the `L` delivery slots. Slot 0 arrives now. -/
abbrev State (L : ℕ) := ℝ≥0 × (Fin L → ℝ≥0)

def initialState (L : ℕ) : State L := (0, fun _ => 0)

def arrival (c : Parameters) (s : State c.L) : ℝ≥0 :=
  s.2 ⟨0, lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos⟩

/-- Inventory recursion uses truncated subtraction on `ℝ≥0`, which is the paper's
positive part. Delivery precedes demand, and today's order enters the last slot. -/
def step (c : Parameters) (s : State c.L) (q d : ℝ≥0) : State c.L :=
  (s.1 + arrival c s - d,
    fun i => if hi : i.val + 1 < c.L then s.2 ⟨i.val + 1, hi⟩ else q)

/-- Zero-start trajectory for any admissible history-dependent policy. -/
def run (c : Parameters) (π : AdmissiblePolicy) (ω : Sample) : ℕ → State c.L
  | 0 => initialState c.L
  | t + 1 => step c (run c π ω t) (order π t ω) (ω.1 t)

def filledDemand (c : Parameters) (s : State c.L) (d : ℝ≥0) : ℝ≥0 :=
  min d (s.1 + arrival c s)

def lostSales (c : Parameters) (s : State c.L) (d : ℝ≥0) : ℝ≥0 :=
  d - (s.1 + arrival c s)

/-- Nonnegative one-period cost `h I_(t+1) + p ell_t`, without a Bochner-integral
fallback to zero for nonintegrable policies. -/
def periodCost (c : Parameters) (s : State c.L) (d : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal c.h * (↑(s.1 + arrival c s - d) : ℝ≥0∞) +
    ENNReal.ofReal c.p * (↑(lostSales c s d) : ℝ≥0∞)

/-- `T + 1` avoids an irrelevant zero-length denominator. This is exactly the
limsup of expected Cesàro costs, with the same limit as horizons `T ≥ 1`. -/
def averageCost (P : DemandLaw) (cost : ℕ → Sample → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ =>
    (∑ t ∈ Finset.range (T + 1), ∫⁻ ω, cost t ω ∂sampleLaw P) /
      (T + 1 : ℝ≥0∞)) Filter.atTop

def policyCost (P : DemandLaw) (c : Parameters) (π : AdmissiblePolicy) : ℝ≥0∞ :=
  averageCost P (fun t ω => periodCost c (run c π ω t) (ω.1 t))

/-- Infimum over *all* admissible policies, not a stationary-policy optimum. -/
def OPT (P : DemandLaw) (c : Parameters) : ℝ≥0∞ :=
  ⨅ π : AdmissiblePolicy, policyCost P c π

/-- Finite-parameter capped base-stock order rule, applied before the delivery
slot is removed from inventory position. -/
def cbsOrder (L : ℕ) (S r : ℝ≥0) (s : State L) : ℝ≥0 :=
  min (S - (s.1 + ∑ i : Fin L, s.2 i)) r

/-- Actual closed-loop capped base-stock trajectory from the same zero state. -/
def cbsRun (c : Parameters) (S r : ℝ≥0) (ω : Sample) : ℕ → State c.L
  | 0 => initialState c.L
  | t + 1 => step c (cbsRun c S r ω t) (cbsOrder c.L S r (cbsRun c S r ω t)) (ω.1 t)

def cbsCost (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) : ℝ≥0∞ :=
  averageCost P (fun t ω => periodCost c (cbsRun c S r ω t) (ω.1 t))

/-- The CBS class uses finite, nonnegative parameters. Ordinary base-stock is
already included by choosing `r = S`; no infinite cap or stock level is used. -/
def CbsOpt (P : DemandLaw) (c : Parameters) : ℝ≥0∞ :=
  ⨅ S : ℝ≥0, ⨅ r : ℝ≥0, cbsCost P c S r

def baseStockCost (P : DemandLaw) (c : Parameters) (S : ℝ≥0) : ℝ≥0∞ :=
  cbsCost P c S S

/-- Exact finite maximum `max_(0 ≤ k ≤ m) sum_(i=1)^k (r-D_i)`.
Demand coordinate 0 here is the manuscript's `D_1`. -/
def finiteInventory (d : DemandPath) (r : ℝ) (m : ℕ) : ℝ :=
  (Finset.range (m + 1)).sup' (by simp) (fun k =>
    ∑ i ∈ Finset.range k, (r - (d i : ℝ)))

/-- The positive-part random variable appearing in each certificate constraint. -/
def certificateExcess (d : DemandPath) (r z : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (finiteInventory d r m +
    (∑ i ∈ Finset.range m, ((d i : ℝ) - r)) - z)

/-- The two distinct horizon constraints of the paper, expressed using genuine
nonnegative expectations; all finite-mean distributions are allowed. -/
def CertificateFeasible (P : DemandLaw) (c : Parameters) (r z : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ mean P ∧ 0 ≤ z ∧
  (∫⁻ d, certificateExcess d r z c.L ∂demandPathLaw P) ≤
    ENNReal.ofReal ((c.L : ℝ) * (mean P - r)) ∧
  (∫⁻ d, certificateExcess d r z (c.L + 1) ∂demandPathLaw P) ≤
    ENNReal.ofReal (((c.L : ℝ) + 1) * (mean P - r))

def certificateObjective (P : DemandLaw) (c : Parameters) (r z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c.h * z + c.p * (mean P - r))

/-- Lower certificate as an extended nonnegative infimum; feasibility is part of
its indexing set, not an assumption that encodes any desired conclusion. -/
def lowerCertificate (P : DemandLaw) (c : Parameters) : ℝ≥0∞ :=
  ⨅ rz : {rz : ℝ × ℝ // CertificateFeasible P c rz.1 rz.2},
    certificateObjective P c rz.val.1 rz.val.2

/-- The exact lead-time-dependent ratio in the main theorem. -/
def rho (L : ℕ) : ℝ := (L : ℝ) / ((L : ℝ) + 1)

def kappa (L : ℕ) : ℝ :=
  1 + 4 * (L : ℝ) ^ 2 / (((L : ℝ) + 1) * (3 * (L : ℝ) - 1))



/-- Complete a finite observed history with zero demands. Future coordinates are
only placeholders: `cbsRun_congr_history` proves that they do not affect the state. -/
def completeHistory (t : ℕ) (a : (Fin t → ℝ≥0) × ℝ) : Sample :=
  (fun k => if hk : k < t then a.1 ⟨k, hk⟩ else 0, a.2)

lemma measurable_completeHistory (t : ℕ) : Measurable (completeHistory t) := by
  unfold completeHistory
  refine Measurable.prodMk (measurable_pi_lambda _ (fun k => ?_)) measurable_snd
  split_ifs <;> fun_prop

lemma measurable_cbsRun (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Measurable (fun ω => cbsRun c S r ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [cbsRun, step, cbsOrder, arrival]
    refine Measurable.prodMk ?_ (measurable_pi_lambda _ (fun i => ?_))
    · fun_prop
    · split_ifs <;> fun_prop

lemma measurable_cbsOrder (L : ℕ) (S r : ℝ≥0) : Measurable (cbsOrder L S r) := by
  unfold cbsOrder
  fun_prop

/-- The CBS feedback rule realized as an admissible measurable history policy. -/
def cbsPolicy (c : Parameters) (S r : ℝ≥0) : AdmissiblePolicy where
  decision t a := cbsOrder c.L S r (cbsRun c S r (completeHistory t a) t)
  measurable_decision t := (measurable_cbsOrder _ _ _).comp
    ((measurable_cbsRun c S r t).comp (measurable_completeHistory t))

lemma cbsRun_congr_history (c : Parameters) (S r : ℝ≥0) (t : ℕ)
    (ω η : Sample) (heq : ∀ k < t, ω.1 k = η.1 k) :
    cbsRun c S r ω t = cbsRun c S r η t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun k hk => heq k (Nat.lt_succ_of_lt hk))
    simp only [cbsRun, hs, heq t (Nat.lt_succ_self t)]

lemma cbsRun_completeHistory (c : Parameters) (S r : ℝ≥0) (t : ℕ) (ω : Sample) :
    cbsRun c S r (completeHistory t (history t ω)) t = cbsRun c S r ω t := by
  apply cbsRun_congr_history
  intro k hk
  simp [completeHistory, history, hk]

lemma run_cbsPolicy (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    run c (cbsPolicy c S r) ω t = cbsRun c S r ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run, ih]
    simp only [order, cbsPolicy, cbsRun_completeHistory, cbsRun]

/-- The directly defined CBS process has exactly the cost of its admissible
policy realization. This removes any gap between the two definitions of cost. -/
lemma policyCost_cbsPolicy (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) :
    policyCost P c (cbsPolicy c S r) = cbsCost P c S r := by
  simp only [policyCost, cbsCost, run_cbsPolicy]

/-- The CBS family is a subclass of the admissible policies in the model. -/
lemma OPT_le_CbsOpt (P : DemandLaw) (c : Parameters) : OPT P c ≤ CbsOpt P c := by
  unfold CbsOpt
  refine le_iInf (fun S => le_iInf (fun r => ?_))
  rw [← policyCost_cbsPolicy]
  exact iInf_le (fun π : AdmissiblePolicy => policyCost P c π) (cbsPolicy c S r)


end CappedBaseStock
