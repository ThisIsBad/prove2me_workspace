import Mathlib

namespace RevenueManagement

/-! ### Single-resource capacity control, Chapter 2 of Talluri and van Ryzin -/

/-! #### The static model, Sect. 2.2 -/

/-- A probability mass function on `ℕ`: nonnegative and summing to one. -/
def IsPmf (f : ℕ → ℝ) : Prop := (∀ d, 0 ≤ f d) ∧ HasSum f 1

/-- The value function `V_j(x)` of the static model, Eq. (2.3): `j` stages (classes) remain, `x`
units of capacity remain, class `j` with price `p j` and demand pmf `f j` arrives at stage `j`, and
`V_0 = 0`. The decision `u` is taken after the demand `d` is seen, `0 ≤ u ≤ min {d, x}`. -/
noncomputable def staticValue (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | j + 1, x => ∑' d, f (j + 1) d *
      (Finset.range (min d x + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
        (fun u => p (j + 1) * u + staticValue p f j (x - u))

/-- The expected marginal value of capacity `ΔV_j(x) = V_j(x) − V_j(x − 1)`, meaningful for `x ≥ 1`. -/
noncomputable def staticDelta (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x : ℕ) : ℝ :=
  staticValue p f j x - staticValue p f j (x - 1)

/-- `u` is an optimal quantity to accept at stage `j + 1` with `x` units remaining and demand `d`:
it is feasible and maximizes `p_{j+1} u + V_j(x − u)` over `0 ≤ u ≤ min {d, x}`, the inner
optimization of (2.3). -/
def IsStageOptimal (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x d u : ℕ) : Prop :=
  u ≤ min d x ∧ ∀ u' ≤ min d x,
    p (j + 1) * u' + staticValue p f j (x - u') ≤ p (j + 1) * u + staticValue p f j (x - u)

open Classical in
/-- The optimal protection level `y_j* = max {x : p_{j+1} < ΔV_j(x)}` of Eq. (2.4), the search over
`x = 1, …, C` and `0` when the set is empty. For `j = 0` it is `0`. -/
noncomputable def protLevel (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (C j : ℕ) : ℕ :=
  ((Finset.range (C + 1)).filter (fun x => 1 ≤ x ∧ p (j + 1) < staticDelta p f j x)).sup id

/-- The nested booking limit `b_j* = C − y_{j−1}*` of Eq. (2.6). -/
noncomputable def bookLimit (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (C j : ℕ) : ℕ :=
  C - protLevel p f C (j - 1)

/-- The stage-`j` bid price `π_j(x) = ΔV_{j−1}(x)` of Eq. (2.7). -/
noncomputable def bidPrice (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x : ℕ) : ℝ :=
  staticDelta p f (j - 1) x

open Classical in
/-- The bid-price control at stage `j + 1`: accept `z` units when `p_{j+1}` is at least the bid
price `π_{j+1}(x + 1 − z)` of the `z`-th unit allocated, i.e. the largest such `z ≤ min {d, x}`, and
`0` when `p_{j+1} < π_{j+1}(x)`. -/
noncomputable def bidControl (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (j x d : ℕ) : ℕ :=
  ((Finset.range (min d x + 1)).filter
    (fun z => z = 0 ∨ bidPrice p f (j + 1) (x + 1 - z) ≤ p (j + 1))).sup id

/-! #### The dynamic model, Sect. 2.5 -/

/-- Arrival probabilities `λ_j(t)` of the dynamic model: at most one request per period, class `j`
with probability `λ_j(t)`, none with the remaining probability. -/
def IsArrivalModel (lam : ℕ → ℕ → ℝ) (n : ℕ) : Prop :=
  (∀ j t, 0 ≤ lam j t) ∧ ∀ t, ∑ j ∈ Finset.Icc 1 n, lam j t ≤ 1

/-- The dynamic value function with `k` periods to go (period `t = T + 1 − k`), Eq. (2.17):
`V(x) = V'(x) + E[max_{u ∈ {0,1}} (R(t) − ΔV'(x)) u]` where `V'` is the value with `k − 1` periods
to go and `R(t) = p_j` with probability `λ_j(t)`, `0` otherwise; `V(0) = 0` and `V = 0` with no
period to go. -/
noncomputable def dynValueGo (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | k + 1, x + 1 =>
      dynValueGo lam p n T k (x + 1) +
        ((∑ j ∈ Finset.Icc 1 n, lam j (T - k) *
            max (p j - (dynValueGo lam p n T k (x + 1) - dynValueGo lam p n T k x)) 0) +
          (1 - ∑ j ∈ Finset.Icc 1 n, lam j (T - k)) *
            max (0 - (dynValueGo lam p n T k (x + 1) - dynValueGo lam p n T k x)) 0)

/-- `V_t(x)` of the dynamic model, Eq. (2.17), for periods `t = 1, …, T + 1`: `V_{T+1} = 0`. -/
noncomputable def dynValue (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x : ℕ) : ℝ :=
  dynValueGo lam p n T (T + 1 - t) x

/-- `ΔV_t(x) = V_t(x) − V_t(x − 1)`. -/
noncomputable def dynDelta (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x : ℕ) : ℝ :=
  dynValue lam p n T t x - dynValue lam p n T t (x - 1)

/-- `u ∈ {0, 1}` is an optimal decision for a class-`j` request in period `t` with `x` units
remaining: it maximizes `(p_j − ΔV_{t+1}(x)) u` over `u ∈ {0, 1}`, the inner optimization of
(2.17). -/
def IsDynOptimal (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x j u : ℕ) : Prop :=
  u ≤ 1 ∧ ∀ u' ≤ 1, (p j - dynDelta lam p n T (t + 1) x) * u' ≤ (p j - dynDelta lam p n T (t + 1) x) * u

open Classical in
/-- The time-dependent protection level `y_j*(t) = max {x : p_{j+1} < ΔV_{t+1}(x)}` of Eq. (2.19),
the search over `x = 1, …, C` and `0` when the set is empty. -/
noncomputable def dynProtLevel (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C t j : ℕ) : ℕ :=
  ((Finset.range (C + 1)).filter
    (fun x => 1 ≤ x ∧ p (j + 1) < dynDelta lam p n T (t + 1) x)).sup id

/-- The time-dependent booking limit `b_j*(t) = C − y_{j−1}*(t)` of Eq. (2.20). -/
noncomputable def dynBookLimit (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C t j : ℕ) : ℕ :=
  C - dynProtLevel lam p n T C t (j - 1)

/-- The bid price `π_t(x) = ΔV_t(x)` of Eq. (2.18). -/
noncomputable def dynBidPrice (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T t x : ℕ) : ℝ :=
  dynDelta lam p n T t x

/-! #### The choice model, Sect. 2.6.2 -/

/-- A discrete-choice model on the classes `Fin n`: `P S j` is the probability that an arriving
customer buys class `j` when the set `S` is offered, with `∑_{j ∈ S} P S j ≤ 1` (the rest is the
no-purchase probability `P_0(S)`). -/
def IsChoiceModel {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) : Prop :=
  (∀ S j, 0 ≤ P S j) ∧ ∀ S, ∑ j ∈ S, P S j ≤ 1

/-- The total purchase probability `Q(S) = ∑_{j ∈ S} P_j(S)`. -/
def purchaseProb {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, P S j

/-- The expected revenue `R(S) = ∑_{j ∈ S} P_j(S) p_j` from offering `S`. -/
def expRevenue {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, P S j * p j

/-- The choice-model value function with `k` periods to go (period `t = T + 1 − k`), Eq. (2.26):
`V(x) = max_{S ⊆ N} λ_t (R(S) − Q(S) ΔV'(x)) + V'(x)`, with `V(0) = 0` and `V = 0` with no period
to go. -/
noncomputable def choiceValueGo {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | k + 1, x + 1 =>
      (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (fun S =>
        lam (T - k) * (expRevenue P p S - purchaseProb P S *
          (choiceValueGo lam P p T k (x + 1) - choiceValueGo lam P p T k x))) +
        choiceValueGo lam P p T k (x + 1)

/-- `V_t(x)` of the choice model, Eq. (2.24)/(2.26), for `t = 1, …, T + 1`: `V_{T+1} = 0`. -/
noncomputable def choiceValue {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T t x : ℕ) : ℝ :=
  choiceValueGo lam P p T (T + 1 - t) x

/-- `ΔV_t(x) = V_t(x) − V_t(x − 1)` for the choice model. -/
noncomputable def choiceDelta {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T t x : ℕ) : ℝ :=
  choiceValue lam P p T t x - choiceValue lam P p T t (x - 1)

/-- The objective `λ_t (R(S) − Q(S) ΔV_{t+1}(x))` of (2.26) for the offer set `S` in period `t`
with `x` units remaining. -/
noncomputable def choiceObj {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T t x : ℕ) (S : Finset (Fin n)) : ℝ :=
  lam t * (expRevenue P p S - purchaseProb P S * choiceDelta lam P p T (t + 1) x)

/-- `S` is an optimal offer set in period `t` with `x` units remaining: it maximizes (2.26). -/
def IsChoiceOptimal {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T t x : ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ S', choiceObj lam P p T t x S' ≤ choiceObj lam P p T t x S

/-- Definition 2.1: `T'` is inefficient if a randomization `α` over the subsets of `N` yields at
most the purchase probability `Q(T')` and strictly more revenue than `R(T')`. -/
def IsInefficient {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (T' : Finset (Fin n)) : Prop :=
  ∃ α : Finset (Fin n) → ℝ, (∀ S, 0 ≤ α S) ∧ ∑ S, α S = 1 ∧
    ∑ S, α S * purchaseProb P S ≤ purchaseProb P T' ∧
    expRevenue P p T' < ∑ S, α S * expRevenue P p S

/-- Definition 2.1: a set is efficient if it is not inefficient. -/
def IsEfficient {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  ¬ IsInefficient P p S

end RevenueManagement
