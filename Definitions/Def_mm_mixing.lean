import Definitions.Def_mm_basic
import Mathlib.Data.Real.Archimedean

/-!
Total variation distance, distance to stationarity, and mixing time,
following Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 4.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **total variation distance**
`‖μ − ν‖_TV = max_{A ⊆ Ω} |μ(A) − ν(A)|` (LPW §4.1, Eq. (4.1)). -/
def tvDist (μ ν : V → ℝ) : ℝ :=
  ⨆ A : Finset V, |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|

/-- The row `P^t(x, ·)`: the distribution after `t` steps started at `x`. -/
def rowDist (P : Matrix V V ℝ) (t : ℕ) (x : V) : V → ℝ :=
  fun y => (P ^ t) x y

/-- `d(t) = max_x ‖P^t(x,·) − π‖_TV`, the worst-case distance to the
stationary distribution after `t` steps (LPW §4.4, Eq. (4.22)). -/
def distStationary (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) : ℝ :=
  ⨆ x : V, tvDist (rowDist P t x) π

/-- `d̄(t) = max_{x,y} ‖P^t(x,·) − P^t(y,·)‖_TV` (LPW §4.4, Eq. (4.23)). -/
def distPairs (P : Matrix V V ℝ) (t : ℕ) : ℝ :=
  ⨆ p : V × V, tvDist (rowDist P t p.1) (rowDist P t p.2)

/-- The **mixing time** `t_mix(ε) = min {t : d(t) ≤ ε}` (LPW §4.5,
Eq. (4.32)). -/
def mixingTime (P : Matrix V V ℝ) (π : V → ℝ) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | distStationary P π t ≤ ε}

/-- `t_mix = t_mix(1/4)` (LPW §4.5, Eq. (4.33)). -/
def tMix (P : Matrix V V ℝ) (π : V → ℝ) : ℕ :=
  mixingTime P π (1 / 4)

/-- A **coupling** of two distributions `μ` and `ν`: a distribution on pairs
whose first marginal is `μ` and second marginal is `ν` (LPW §4.2). -/
def IsCoupling (μ ν : V → ℝ) (q : V × V → ℝ) : Prop :=
  IsDist q ∧ (∀ x : V, ∑ y, q (x, y) = μ x) ∧ ∀ y : V, ∑ x, q (x, y) = ν y

/-- The **inverse distribution** `μ̂(g) = μ(g⁻¹)` of an increment distribution
on a group; the walk with increments `μ̂` is the time reversal of the walk
with increments `μ` (LPW §4.6). -/
def invDist {G : Type*} [Group G] (μ : G → ℝ) : G → ℝ :=
  fun g => μ g⁻¹

end

end MarkovMixing
