import Mathlib

namespace LubyMIS.MonteCarlo

open Finset

/-- The neighbourhood `N(W) = {i ∈ V′ : ∃ j ∈ W, (i, j) ∈ E′}` of a vertex set `W` in the current
graph `H = G′` (Luby 1986, §3.1, p. 1038). -/
def nbhd {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V) :
    Finset V :=
  Finset.univ.filter (fun i => ∃ j ∈ W, H.Adj i j)

open Classical in
/-- The number of edges eliminated by one execution of the loop body that selects `I′`: the edges of
`H` with at least one endpoint in `Y = I′ ∪ N(I′)`. The induced subgraph on `V′ − Y` keeps exactly the
other edges, so this is `Y_k − Y_{k+1}` (§3.1, p. 1039; §3.4, p. 1040). -/
noncomputable def eliminated {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (I' : Finset V) : ℕ :=
  (H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ I' ∪ nbhd H I')).card

/-- `sum(i) = ∑_{j ∈ adj(i)} 1 / d(j)` (§3.4, p. 1041). The page defines it only for `d(i) ≥ 1`; at
`d(i) = 0` this is the empty sum `0`. -/
noncomputable def sumInv {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) : ℝ :=
  ∑ j ∈ H.neighborFinset i, 1 / (H.degree j : ℝ)

/-- Algorithm A's select step (§3.2, pp. 1039–1040) for the priorities `π`: ALGEDGE runs on both
orientations of every edge, so `i` survives iff `π(i) < π(j)` for every neighbour `j`. -/
def selectA {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (π : V → ℕ) :
    Finset V :=
  Finset.univ.filter (fun i => ∀ j, H.Adj i j → π i < π j)

/-- Algorithm B's select step (§3.3, p. 1040) for the coin values `c` (`X = {i : c i = true}`,
`I′` starting at `X`): `i ∈ X` survives iff every neighbour `j ∈ X` has `d(j) < d(i)`. -/
def selectB {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (c : V → Bool) :
    Finset V :=
  Finset.univ.filter (fun i => c i = true ∧ ∀ j, H.Adj i j → c j = true → H.degree j < H.degree i)

/-- Algorithm A's priority values: `π(i) = (π₀ i : ℕ) + 1 ∈ {1, …, n⁴}` for `π₀ : V → Fin (n ^ 4)`. -/
def prioA {V : Type*} {n : ℕ} (π₀ : V → Fin (n ^ 4)) : V → ℕ :=
  fun i => (π₀ i : ℕ) + 1

open Classical in
/-- Probability of an event `P` of the priority vector under Algorithm A's law: the priorities are
mutually independent and uniform on `{1, …, n⁴}`, i.e. the uniform law on the `(n⁴)^{|V|}` vectors. -/
noncomputable def probA {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (P : (V → ℕ) → Prop) : ℝ :=
  ((Finset.univ.filter (fun π₀ : V → Fin (n ^ 4) => P (prioA π₀))).card : ℝ) /
    ((n : ℝ) ^ 4) ^ Fintype.card V

/-- Expectation of a real function of the priority vector under Algorithm A's law. -/
noncomputable def expA {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (f : (V → ℕ) → ℝ) : ℝ :=
  (∑ π₀ : V → Fin (n ^ 4), f (prioA π₀)) / ((n : ℝ) ^ 4) ^ Fintype.card V

/-- `Pr[coin(i) = 1]` in Algorithm B (§3.3, p. 1040): `1/(2 d(i))` if `d(i) ≥ 1`, and `1` if `d(i) = 0`. -/
noncomputable def coinProb {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) : ℝ :=
  if 1 ≤ H.degree i then 1 / (2 * (H.degree i : ℝ)) else 1

/-- The probability of the coin vector `c` in Algorithm B: the coins are mutually independent, so the
law is the product of the marginals. -/
noncomputable def lawB {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : V → Bool) : ℝ :=
  ∏ i, if c i then coinProb H i else 1 - coinProb H i

open Classical in
/-- Probability of an event `P` of the coin vector under Algorithm B's law. -/
noncomputable def probB {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (P : (V → Bool) → Prop) : ℝ :=
  ∑ c : V → Bool, if P c then lawB H c else 0

/-- Expectation of a real function of the coin vector under Algorithm B's law. -/
noncomputable def expB {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (f : (V → Bool) → ℝ) : ℝ :=
  ∑ c : V → Bool, lawB H c * f c

end LubyMIS.MonteCarlo
