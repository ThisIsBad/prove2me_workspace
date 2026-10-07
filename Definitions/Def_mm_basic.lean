import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
Basic vocabulary of finite Markov chains, following Levin–Peres–Wilmer,
*Markov Chains and Mixing Times*, Chapter 1.

A chain on a finite state space `V` is presented by its transition matrix
`P : Matrix V V ℝ`, acting on the right of row vectors: a distribution `μ`
evolves to `μ ᵥ* P` in one step, and the `t`-step transition probabilities
are the entries of `P ^ t`.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matrix is **stochastic** (a transition matrix) if its entries are
nonnegative and every row sums to `1` (LPW §1.1, Eq. (1.1)). -/
def IsStochastic (P : Matrix V V ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- A **probability distribution** on the finite state space `V`, presented as a
row vector: nonnegative entries summing to `1`. -/
def IsDist (μ : V → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- A distribution `π` is **stationary** for `P` if `π = π P` (LPW §1.1, Eq. (1.4)). -/
def IsStationary (P : Matrix V V ℝ) (π : V → ℝ) : Prop :=
  IsDist π ∧ Matrix.vecMul π P = π

/-- A chain is **irreducible** if any state can reach any other: for all
`x y` there is a `t` with `P^t(x,y) > 0` (LPW §1.3). -/
def Irreducible (P : Matrix V V ℝ) : Prop :=
  ∀ x y : V, ∃ t : ℕ, 0 < (P ^ t) x y

/-- `T(x) = {t ≥ 1 : P^t(x,x) > 0}`, the set of possible return times to `x`
(LPW §1.3). -/
def returnSet (P : Matrix V V ℝ) (x : V) : Set ℕ :=
  {t : ℕ | 1 ≤ t ∧ 0 < (P ^ t) x x}

/-- The **period** of a state `x` is `gcd T(x)` (LPW §1.3).  It is formalized as
the largest natural number dividing every element of `returnSet P x` (which is
the gcd whenever `T(x) ≠ ∅`, and junk-value `0` when `T(x) = ∅`). -/
def period (P : Matrix V V ℝ) (x : V) : ℕ :=
  sSup {d : ℕ | ∀ t ∈ returnSet P x, d ∣ t}

/-- A chain is **aperiodic** if every state has period `1` (LPW §1.3). -/
def Aperiodic (P : Matrix V V ℝ) : Prop :=
  ∀ x : V, period P x = 1

/-- The **lazy version** `Q = (I + P)/2` of a chain (LPW §1.3). -/
def lazy (P : Matrix V V ℝ) : Matrix V V ℝ :=
  (2⁻¹ : ℝ) • (1 : Matrix V V ℝ) + (2⁻¹ : ℝ) • P

/-- A function `h` is **harmonic** for `P` (at every state) if
`h(x) = ∑_y P(x,y) h(y)` (LPW §1.5.4, Eq. (1.28)). -/
def Harmonic (P : Matrix V V ℝ) (h : V → ℝ) : Prop :=
  ∀ x : V, h x = ∑ y, P x y * h y

/-- `π` and `P` are in **detailed balance** if `π(x) P(x,y) = π(y) P(y,x)` for
all `x, y`; a chain admitting such a distribution is called reversible
(LPW §1.6, Eq. (1.30)). -/
def DetailedBalance (P : Matrix V V ℝ) (π : V → ℝ) : Prop :=
  ∀ x y : V, π x * P x y = π y * P y x

/-- The **time reversal** `P̂(x,y) = π(y) P(y,x) / π(x)` of a chain with
stationary distribution `π` (LPW §1.6, Eq. (1.33)). -/
def timeReversal (P : Matrix V V ℝ) (π : V → ℝ) : Matrix V V ℝ :=
  fun x y => π y * P y x / π x

/-- **Simple random walk** on a graph `G`: from `x`, move to a uniformly chosen
neighbor of `x` (LPW §1.4, Eq. (1.13)). -/
def graphWalk (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun x y => if G.Adj x y then ((G.degree x : ℝ))⁻¹ else 0

/-- The **uniform distribution** on a finite state space. -/
def uniformDist (V : Type*) [Fintype V] : V → ℝ :=
  fun _ => (Fintype.card V : ℝ)⁻¹

/-- The **random walk on a finite group** `G` with increment distribution `μ`:
from `a`, move to `h * a` where `h ∼ μ`, so the transition probability from
`a` to `b` is `μ (b * a⁻¹)` (LPW §2.6). -/
def groupWalk {G : Type*} [Group G] [Fintype G] (μ : G → ℝ) : Matrix G G ℝ :=
  fun a b => μ (b * a⁻¹)

end

end MarkovMixing
