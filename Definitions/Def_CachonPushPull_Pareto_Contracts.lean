import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- The two single-wholesale-price contract types of §4.4. -/
inductive Mode
  | push
  | pull
  deriving DecidableEq

/-- A single-wholesale-price contract: a mode and a quantity `q` (the retailer's prebook with
push, the supplier's production with pull). The wholesale price is the one that induces `q`:
`ŵ₁(q)` for push, `w₁(q)` for pull. -/
structure Contract where
  mode : Mode
  q : ℝ

/-- The contract's wholesale price: `ŵ₁(q)` for push, `w₁(q)` for pull. -/
noncomputable def Contract.wholesalePrice (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : ℝ :=
  match k.mode with
  | .push => pushPrice μ p v k.q
  | .pull => pullPrice μ c v k.q

/-- The retailer's expected profit under a contract: `π̂_r(q)` for push, `π_r(q)` for pull. -/
noncomputable def Contract.retailerPayoff (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : ℝ :=
  match k.mode with
  | .push => pushRetailerProfit μ p v k.q
  | .pull => pullRetailerProfit μ p c v k.q

/-- The supplier's expected profit under a contract: `π̂_s(q)` for push, `π_s(q)` for pull. -/
noncomputable def Contract.supplierPayoff (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : ℝ :=
  match k.mode with
  | .push => pushSupplierProfit μ p c v k.q
  | .pull => pullSupplierProfit μ c v k.q

/-- An admissible contract: quantity `q ≥ 0` and wholesale price between the production cost and
the retail price, `c ≤ w ≤ p`. -/
def Contract.IsAdmissible (μ : Measure ℝ) (p c v : ℝ) (k : Contract) : Prop :=
  0 ≤ k.q ∧ c ≤ k.wholesalePrice μ p c v ∧ k.wholesalePrice μ p c v ≤ p

/-- `k'` Pareto dominates `k`: no firm is worse off under `k'` and one firm is strictly better
off (p. 224). -/
def Contract.ParetoDominates (μ : Measure ℝ) (p c v : ℝ) (k' k : Contract) : Prop :=
  k.retailerPayoff μ p c v ≤ k'.retailerPayoff μ p c v ∧
  k.supplierPayoff μ p c v ≤ k'.supplierPayoff μ p c v ∧
  (k.retailerPayoff μ p c v < k'.retailerPayoff μ p c v ∨
    k.supplierPayoff μ p c v < k'.supplierPayoff μ p c v)

/-- The Pareto set among the admissible push and pull contracts: admissible contracts that no
admissible contract Pareto dominates. -/
def paretoSet (μ : Measure ℝ) (p c v : ℝ) : Set Contract :=
  {k | k.IsAdmissible μ p c v ∧ ¬ ∃ k' : Contract, k'.IsAdmissible μ p c v ∧ k'.ParetoDominates μ p c v k}

end CachonPushPull.Pareto
