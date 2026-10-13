import Mathlib

namespace RossQC.Regions

open Filter Topology

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, pp. 587–588, §1–§2: the data of the general model.

* `ι` is the countable set of underlying states `0, 1, 2, …`; `i₀` is the state `0` that a
  revision leads to.
* `Pm i j = P_ij` is the probability of moving from state `i` (at the end of a period) to state `j`
  (at the beginning of the next).
* `C i`, `I i`, `R i` are the costs `C_i` (produce without inspection), `I_i` (produce with
  inspection) and `R_i` (revise) in state `i`.
* `β` is the discount factor.

The hypotheses the paper places on these data are collected in `Model.Valid`. -/
structure Model (ι : Type*) where
  /-- The state `0` reached by a revision. -/
  i₀ : ι
  /-- The transition matrix `P_ij`. -/
  Pm : ι → ι → ℝ
  /-- `C_i`, the cost of producing without inspection in state `i`. -/
  C : ι → ℝ
  /-- `I_i`, the cost of producing with inspection in state `i`. -/
  I : ι → ℝ
  /-- `R_i`, the cost of revising in state `i`. -/
  R : ι → ℝ
  /-- The discount factor `β`. -/
  β : ℝ

/-- The standing hypotheses of §1–§2 (pp. 587–588): `P_ij` is a stochastic matrix (nonnegative
entries, every row summing to `1`, as a `HasSum`), "all costs are bounded", and `β ∈ (0, 1)`. No
sign condition is placed on the costs. -/
structure Model.Valid {ι : Type*} [Countable ι] (M : Model ι) : Prop where
  Pm_nonneg : ∀ i j, 0 ≤ M.Pm i j
  Pm_row : ∀ i, HasSum (M.Pm i) 1
  costs_bdd : ∃ B : ℝ, ∀ i, |M.C i| ≤ B ∧ |M.I i| ≤ B ∧ |M.R i| ≤ B
  β_pos : 0 < M.β
  β_lt_one : M.β < 1

/-- The three actions of §2: produce without inspection (**P**), produce with inspection (**I**),
revise the process (**R**). -/
inductive Action
  | produce
  | inspect
  | revise
  deriving DecidableEq

variable {ι : Type*}

/-- The state space `S = {P = (P₀, P₁, ⋯) : P_i ≥ 0, Σ_i P_i = 1}` of §2, p. 588. The sum is a
`HasSum`, so `P` is a genuine probability vector. -/
def Model.simplex (_M : Model ι) : Set (ι → ℝ) :=
  {P | (∀ i, 0 ≤ P i) ∧ HasSum P 1}

/-- `TP`, p. 588: `(TP)_i = Σ_j P_j P_ji`, the belief one period later when the item is produced
without inspection. -/
noncomputable def Model.T (M : Model ι) (P : ι → ℝ) : ι → ℝ :=
  fun i => ∑' j, P j * M.Pm j i

/-- `e^i = (P_i0, P_i1, ⋯)`, p. 588: the belief one period later when the process is known to be in
state `i` (after an inspection revealing `i`, and `e⁰` after a revision). -/
def Model.e (M : Model ι) (i : ι) : ι → ℝ :=
  M.Pm i

/-- The right side of the optimality equation (1), p. 588, for a function `V` on beliefs, at the
belief `P` and the action `a`:

* produce: `Σ P_iC_i + βV(TP)`;
* inspect: `Σ P_iI_i + β Σ P_iV(e^i)`;
* revise: `Σ P_iR_i + βV(e⁰)`. -/
noncomputable def Model.rhs (M : Model ι) (V : (ι → ℝ) → ℝ) (P : ι → ℝ) : Action → ℝ
  | .produce => (∑' i, P i * M.C i) + M.β * V (M.T P)
  | .inspect => (∑' i, P i * M.I i) + M.β * ∑' i, P i * V (M.e i)
  | .revise => (∑' i, P i * M.R i) + M.β * V (M.e M.i₀)

/-- The Bellman operator: the minimum over the three actions of the right side of (1). -/
noncomputable def Model.bellman (M : Model ι) (V : (ι → ℝ) → ℝ) (P : ι → ℝ) : ℝ :=
  min (M.rhs V P .produce) (min (M.rhs V P .inspect) (M.rhs V P .revise))

/-- Value iteration, as in the proof of Lemma 2.1, p. 589: `V⁰ = 0` and
`V^{n+1}(P) = min{Σ P_iC_i + βV^n(TP); Σ P_iI_i + β Σ P_iV^n(e^i); Σ P_iR_i + βV^n(e⁰)}`, so that
`V¹(P) = min{Σ P_iC_i, Σ P_iI_i, Σ P_iR_i}` is the paper's `V_β¹`. -/
noncomputable def Model.valueIter (M : Model ι) : ℕ → (ι → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => M.bellman (M.valueIter n)

/-- The β-discounted optimal cost `V_β(P) = lim_n V^n(P)`.

**Formalization Note.** The paper defines `V_β(P)` as the infimum, over all (measurable) policies,
of the expected discounted cost `ψ(P, β, R)`, and notes in the proof of Lemma 2.1 (p. 589) that
`V^n(P)` is the minimal expected cost over `n` stages, so that `V^n(P) → V_β(P)`. This file takes
that limit as the definition (`limUnder`); the existence of the limit on `S` is part of the
milestone formalizing (1). -/
noncomputable def Model.Vβ (M : Model ι) (P : ι → ℝ) : ℝ :=
  limUnder atTop (fun n => M.valueIter n P)

/-- The β-optimal region of the action `a` (Definition, p. 588): the beliefs `P ∈ S` at which
`a` attains the minimum in (1), i.e. `V_β(P)` equals the right side of (1) for `a`. -/
def Model.region (M : Model ι) (a : Action) : Set (ι → ℝ) :=
  {P | P ∈ M.simplex ∧ M.Vβ P = M.rhs M.Vβ P a}

/-- The β-optimal produce region `{P : V_β(P) = Σ P_iC_i + βV_β(TP)}`, p. 588. -/
def Model.produceRegion (M : Model ι) : Set (ι → ℝ) := M.region .produce

/-- The β-optimal inspect region `{P : V_β(P) = Σ P_iI_i + β Σ P_iV_β(e^i)}`, p. 588. -/
def Model.inspectRegion (M : Model ι) : Set (ι → ℝ) := M.region .inspect

/-- The β-optimal revise region `{P : V_β(P) = Σ P_iR_i + βV_β(e⁰)}`, p. 588. -/
def Model.reviseRegion (M : Model ι) : Set (ι → ℝ) := M.region .revise

end RossQC.Regions
