import Mathlib

namespace SerfozoStochasticNetworks

variable {E : Type*}

/-- The **detailed balance** equations `π(x) q(x,y) = π(y) q(y,x)`.
Serfozo, *Introduction to Stochastic Networks*, (2.1). -/
def DetailedBalance (q : E → E → ℝ) (π : E → ℝ) : Prop := ∀ x y, π x * q x y = π y * q y x

/-- A transition rate function is **reversible** when some positive measure satisfies its detailed
balance equations. Serfozo, Definition 1.4 and section 2.1. -/
def IsReversible (q : E → E → ℝ) : Prop := ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ DetailedBalance q π

/-- The **two-way communication** property: `q(x,y)` and `q(y,x)` are positive together.
Serfozo, section 2.1. -/
def TwoWay (q : E → E → ℝ) : Prop := ∀ x y, 0 < q x y ↔ 0 < q y x

/-- `x₀, …, x_n` is a **path** when every consecutive transition has positive rate.
Serfozo, section 2.3. -/
def IsPath (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : Prop :=
  ∀ i : Fin n, 0 < q (p i.castSucc) (p i.succ)

/-- The product of the rates along a path, read forwards. -/
def pathRate (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : ℝ :=
  ∏ i : Fin n, q (p i.castSucc) (p i.succ)

/-- The product of the rates along a path, read backwards. -/
def pathRateRev (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : ℝ :=
  ∏ i : Fin n, q (p i.succ) (p i.castSucc)

/-- The product of the rate ratios `ρ(x,y) = q(x,y)/q(y,x)` along a path; the right-hand side of
Serfozo's expression (2.9). -/
noncomputable def pathRatio (q : E → E → ℝ) {n : ℕ} (p : Fin (n + 1) → E) : ℝ :=
  ∏ i : Fin n, q (p i.castSucc) (p i.succ) / q (p i.succ) (p i.castSucc)

/-- **Kolmogorov's criterion**: around every closed path the forward and backward products of the
rates agree. Serfozo, Theorem 2.8 (ii). -/
def KolmogorovCriterion (q : E → E → ℝ) : Prop :=
  ∀ (n : ℕ) (p : Fin (n + 1) → E), p 0 = p (Fin.last n) → pathRate q p = pathRateRev q p

/-- The ratio form of Kolmogorov's criterion: the product of rate ratios along a path depends on
the path only through its endpoints. Serfozo, Theorem 2.8 (iii). -/
def RatioInvariance (q : E → E → ℝ) : Prop :=
  ∀ (n n' : ℕ) (p : Fin (n + 1) → E) (p' : Fin (n' + 1) → E), IsPath q p → IsPath q p' →
    p 0 = p' 0 → p (Fin.last n) = p' (Fin.last n') → pathRatio q p = pathRatio q p'

/-- Irreducibility: every state is reachable from every other along a path. -/
def IsIrreducible (q : E → E → ℝ) : Prop :=
  ∀ x y : E, ∃ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p ∧ p 0 = x ∧ p (Fin.last n) = y

/-- `π` is an **invariant measure** of `q`: the total flow out of each state balances the flow in.
Serfozo, section 2.1. -/
def IsInvariant (q : E → E → ℝ) (π : E → ℝ) : Prop :=
  ∀ x, π x * ∑' y, q x y = ∑' y, π y * q y x

/-- The **communication graph** of `q`: an undirected graph on the state space with an edge
between distinct `x` and `y` when either rate between them is non-zero. Serfozo, section 2.1. -/
def commGraph (q : E → E → ℝ) : SimpleGraph E :=
  SimpleGraph.fromRel fun x y => q x y ≠ 0

/-- The transition rates of a **birth-death process** on `ℕ`: arrivals at rate `lam x` and
departures at rate `mu x`. Serfozo, Example 2.1. -/
def birthDeathRate (lam mu : ℕ → ℝ) (x y : ℕ) : ℝ :=
  if y = x + 1 then lam x else if x = y + 1 then mu x else 0

/-- The measure `π(x) = ∏_{n=1}^{x} λ(n-1)/μ(n)` of Serfozo (2.3), normalized so `π(0) = 1`. -/
noncomputable def birthDeathMeasure (lam mu : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∏ n ∈ Finset.range x, lam n / mu (n + 1)

end SerfozoStochasticNetworks
