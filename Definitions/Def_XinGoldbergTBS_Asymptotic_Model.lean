import Mathlib

/-!
# Dual-sourcing backlog inventory model (Xin and Goldberg 2018, Section 2)

Periods are the paper's `t = 1, 2, …`. Orders are stored as integer-indexed histories
`q^R_k`, `q^E_k` (`k : ℤ`), equal to `0` for every `k ≤ 0` and for every period not yet
reached. `run π ω n` is the state at the start of period `n + 1`: the orders placed in periods
`≤ n` and the on-hand inventory `I_{n+1}`.

The sample space carries three independent objects: the current demands `D₁, D₂, …`
(coordinate `n` is `D_{n+1}`), the initial-condition demands `D'₋₁, D'₋₂, …` (coordinate `n`
is `D'_{-(n+1)}`), and `Ĝ` with `ℙ(Ĝ = k) = 2^{-k}`, `k ≥ 1`. The paper's regular unit cost is
`c_R = 0` (p. 440), so `c = c_E - c_R` is the only purchase cost, charged per express unit.
Costs are `ℝ≥0∞`-valued, so infinite expected or long-run costs are kept as `∞`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- The demand distribution `D`: a probability law on `ℝ` carried by `[0, ∞)`, with finite
mean, and not a point mass (the paper's "strictly positive (possibly infinite) variance"). -/
structure DemandLaw where
  law : Measure ℝ
  isProb : IsProbabilityMeasure law
  nonneg : law (Set.Iio 0) = 0
  integrable : Integrable id law
  nondegenerate : ∀ a : ℝ, law {a} < 1

attribute [instance] DemandLaw.isProb

/-- `𝔼[D]`. -/
def DemandLaw.mean (μ : DemandLaw) : ℝ := ∫ d, d ∂μ.law

/-- Unit backorder cost `b`, unit holding cost `h`, and express premium `c = c_E - c_R`
(with `c_R = 0`). -/
structure Costs where
  b : ℝ
  h : ℝ
  c : ℝ
  b_pos : 0 < b
  h_pos : 0 < h
  c_pos : 0 < c

/-- `G(y) = h y⁺ + b y⁻`. -/
def G (κ : Costs) (y : ℝ) : ℝ := κ.h * max y 0 + κ.b * max (-y) 0

/-- Law of `Ĝ`: mass `2^{-k}` at each `k ≥ 1`. -/
def ghatLaw : Measure ℕ :=
  Measure.sum fun k : ℕ => ((1 / 2 : ℝ≥0) ^ (k + 1)) • Measure.dirac (k + 1)

/-- A demand path; coordinate `n` is the paper's demand with 1-based index `n + 1`. -/
abbrev Path := ℕ → ℝ

/-- Sample point `(D, D', Ĝ)`. -/
abbrev Sample := Path × Path × ℕ

/-- I.i.d. demand path law. -/
def pathLaw (μ : DemandLaw) : Measure Path := Measure.infinitePi fun _ : ℕ => μ.law

/-- Law of `(D, D', Ĝ)`: independent components. -/
def sampleLaw (μ : DemandLaw) : Measure Sample :=
  (pathLaw μ).prod ((pathLaw μ).prod ghatLaw)

/-- Argument of an admissible policy in period `t`:
`(q^R_{t-L}, …, q^R_{t-1})`, `(q^E_{t-L₀}, …, q^E_{t-1})`, `I_t` — a point of `ℝ^{L+L₀+1}`. -/
abbrev Obs (L₀ L : ℕ) := (Fin L → ℝ) × (Fin L₀ → ℝ) × ℝ

/-- The paper's class `Π` (p. 440): a sequence of deterministic measurable maps `f_t`
(`t ≥ 1`; the value at `t = 0` is never used) from `ℝ^{L+L₀+1}` to `ℝ₊²`, returning
(regular order, express order). -/
structure AdmissiblePolicy (L₀ L : ℕ) where
  f : ℕ → Obs L₀ L → ℝ≥0 × ℝ≥0
  measurable_f : ∀ t, Measurable (f t)

/-- State: regular order history, express order history, on-hand inventory. -/
abbrev State := (ℤ → ℝ) × (ℤ → ℝ) × ℝ

/-- The policy's argument in period `t`, read off the state at the start of period `t`. -/
def observe (L₀ L : ℕ) (t : ℕ) (s : State) : Obs L₀ L :=
  (fun i => s.1 ((t : ℤ) - L + i), fun i => s.2.1 ((t : ℤ) - L₀ + i), s.2.2)

/-- Initial condition: no orders, inventory `-∑_{i=1}^{Ĝ} D'_{-i}`. -/
def initState (ω : Sample) : State :=
  (0, 0, -∑ i ∈ Finset.range ω.2.2, ω.2.1 i)

/-- Period `t`: orders `a = (q^R_t, q^E_t)` are placed, `q^R_{t-L} + q^E_{t-L₀}` arrives, demand
`d = D_t` is realized: `I_{t+1} = I_t + q^R_{t-L} + q^E_{t-L₀} - D_t`. -/
def step (L₀ L : ℕ) (t : ℕ) (a : ℝ≥0 × ℝ≥0) (d : ℝ) (s : State) : State :=
  let qR := Function.update s.1 (t : ℤ) (a.1 : ℝ)
  let qE := Function.update s.2.1 (t : ℤ) (a.2 : ℝ)
  (qR, qE, s.2.2 + qR ((t : ℤ) - L) + qE ((t : ℤ) - L₀) - d)

/-- `run π ω n`: state at the start of period `n + 1` under policy `π`. -/
def run {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (ω : Sample) : ℕ → State
  | 0 => initState ω
  | n + 1 =>
      step L₀ L (n + 1) (π.f (n + 1) (observe L₀ L (n + 1) (run π ω n))) (ω.1 n) (run π ω n)

/-- `C_t = c q^E_{t-L₀} + G(I_t + q^R_{t-L} + q^E_{t-L₀} - D_t)` (with `c_R = 0`), for period
`t ≥ 1`; the state `run π ω t` is the one after period `t`, whose inventory is `I_{t+1}`. -/
def periodCost (κ : Costs) {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (ω : Sample) (t : ℕ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (κ.c * (run π ω t).2.1 ((t : ℤ) - L₀)) + ENNReal.ofReal (G κ (run π ω t).2.2)

/-- `C(π) = limsup_{T→∞} (∑_{t=L₀+1}^{T} 𝔼[C_t^π]) / T`. -/
def policyCost (μ : DemandLaw) (κ : Costs) {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ =>
    (∑ t ∈ Finset.Icc (L₀ + 1) T, ∫⁻ ω, periodCost κ π ω t ∂sampleLaw μ) / (T : ℝ≥0∞))
    Filter.atTop

/-- `OPT(L) = inf_{π ∈ Π} C(π)`. -/
def OPT (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) : ℝ≥0∞ :=
  ⨅ π : AdmissiblePolicy L₀ L, policyCost μ κ π

/-- Expedited inventory position computed from a policy argument:
`Î_t = I_t + ∑_{k=t-L₀}^{t-1} q^E_k + ∑_{k=t-L}^{t-L+L₀} q^R_k`. -/
def expeditedPosition {L₀ L : ℕ} (o : Obs L₀ L) : ℝ :=
  o.2.2 + ∑ i, o.2.1 i + ∑ i ∈ Finset.univ.filter (fun i : Fin L => i.val ≤ L₀), o.1 i

/-- Truncated regular pipeline `ℛ^t = (q^R_{t-L+L₀+1}, …, q^R_{t-1})`; 0-based coordinate `j`
is the paper's `ℛ^t_{j+1} = q^R_{t-L+L₀+1+j}`. -/
def truncPipeline {L₀ L : ℕ} (o : Obs L₀ L) : Fin (L - L₀ - 1) → ℝ :=
  fun j => o.1 ⟨L₀ + 1 + j.val, by have := j.isLt; omega⟩

lemma measurable_expeditedPosition (L₀ L : ℕ) :
    Measurable (fun o : Obs L₀ L => expeditedPosition o) := by
  unfold expeditedPosition
  fun_prop

lemma measurable_truncPipeline (L₀ L : ℕ) :
    Measurable (fun o : Obs L₀ L => truncPipeline o) := by
  unfold truncPipeline
  fun_prop

/-- The paper's class `Π̂` (p. 440): measurable maps `f̂_t` from `ℝ^{L-L₀}` (the truncated
regular pipeline and the expedited inventory position) to `ℝ₊²`. -/
structure ReducedPolicy (L₀ L : ℕ) where
  f : ℕ → (Fin (L - L₀ - 1) → ℝ) × ℝ → ℝ≥0 × ℝ≥0
  measurable_f : ∀ t, Measurable (f t)

/-- A `Π̂` policy seen as a member of `Π`. -/
def ReducedPolicy.toPolicy {L₀ L : ℕ} (π : ReducedPolicy L₀ L) : AdmissiblePolicy L₀ L where
  f t o := π.f t (truncPipeline o, expeditedPosition o)
  measurable_f t := (π.measurable_f t).comp
    ((measurable_truncPipeline L₀ L).prodMk (measurable_expeditedPosition L₀ L))

/-- `inf_{π ∈ Π̂} C(π)`. -/
def OPThat (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) : ℝ≥0∞ :=
  ⨅ π : ReducedPolicy L₀ L, policyCost μ κ π.toPolicy

/-- The TBS policy `π_{r,S}` (p. 440): `q^R_t = r`, `q^E_t = max(0, S - Î_t)`. It is used
only with `r ≥ 0`; `r.toNNReal` is then `r`. -/
def tbsPolicy (L₀ L : ℕ) (r S : ℝ) : AdmissiblePolicy L₀ L where
  f _ o := (r.toNNReal, (S - expeditedPosition o).toNNReal)
  measurable_f _ := measurable_const.prodMk
    ((measurable_const.sub (measurable_expeditedPosition L₀ L)).real_toNNReal)

/-- `C(π_{r,S})`. -/
def tbsCost (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r S : ℝ) : ℝ≥0∞ :=
  policyCost μ κ (tbsPolicy L₀ L r S)

/-- `F^∞(r) = inf_{S ∈ ℝ} C(π_{r,S})`. -/
def Finf (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ⨅ S : ℝ, tbsCost μ κ L₀ L r S

/-- `(r*, S*)` is a best TBS pair (p. 441): `r* ∈ argmin_{0 ≤ r ≤ 𝔼[D]} F^∞(r)` and
`S* ∈ argmin_{S ∈ ℝ} C(π_{r*,S})`. -/
def IsBestTBS (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (r S : ℝ) : Prop :=
  r ∈ Set.Icc 0 μ.mean ∧
  (∀ r' ∈ Set.Icc 0 μ.mean, Finf μ κ L₀ L r ≤ Finf μ κ L₀ L r') ∧
  ∀ S' : ℝ, tbsCost μ κ L₀ L r S ≤ tbsCost μ κ L₀ L r S'

end XinGoldbergTBS.Asymptotic
