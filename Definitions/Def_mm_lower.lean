import Definitions.Def_mm_mixing
import Definitions.Def_mm_coupling
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
Quantities used in lower bounds on mixing times, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 7.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The maximal number of states accessible in one step,
`Δ = max_x |{y : P(x,y) > 0}|` (LPW §7.1.1, Eq. (7.1)). -/
def maxOutDegree (P : Matrix V V ℝ) : ℕ :=
  Finset.univ.sup fun x : V => (Finset.univ.filter fun y : V => 0 < P x y).card

/-- The graph underlying a chain: an edge between `x ≠ y` whenever
`P(x,y) + P(y,x) > 0`; the chain's **diameter** is this graph's diameter
(LPW §7.1.2). -/
def transGraph (P : Matrix V V ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => 0 < P x y

/-- The **edge measure** `Q(x,y) = π(x) P(x,y)` (LPW §7.2, Eq. (7.4)). -/
def edgeMeasure (P : Matrix V V ℝ) (π : V → ℝ) (x y : V) : ℝ :=
  π x * P x y

/-- The **bottleneck ratio** `Φ(S) = Q(S, Sᶜ)/π(S)` of a set of states
(LPW §7.2, Eq. (7.5)). -/
def bottleneckRatio (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) : ℝ :=
  (∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y) / ∑ x ∈ S, π x

/-- The **bottleneck ratio of the chain**,
`Φ⋆ = min {Φ(S) : π(S) ≤ 1/2, S ≠ ∅}` (LPW §7.2, Eq. (7.6)). -/
def bottleneckStar (P : Matrix V V ℝ) (π : V → ℝ) : ℝ :=
  ⨅ S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹},
    bottleneckRatio P π S.1

/-- The expectation `E_μ(f) = ∑_x f(x) μ(x)` of a statistic under a
distribution (LPW §7.3). -/
def distExp (μ : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, f x * μ x

/-- The variance `Var_μ(f)` of a statistic under a distribution (LPW §7.3). -/
def distVar (μ : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ x, (f x - distExp μ f) ^ 2 * μ x

/-- The pushforward `μ f⁻¹` of a distribution under a statistic
`f : Ω → Λ` (LPW §7.3). -/
def pushforward {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (μ : V → ℝ) (f : V → Λ) :
    Λ → ℝ :=
  fun b => ∑ a ∈ Finset.univ.filter fun a : V => f a = b, μ a

/-- The **lazy random walk on the `n`-dimensional hypercube** `{0,1}^n`
(LPW §2.3): the hypercube is the torus `ℤ_2^n`. -/
def hypercubeWalk (n : ℕ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  lazy (graphWalk (torusGraph n 2))

end

end MarkovMixing
