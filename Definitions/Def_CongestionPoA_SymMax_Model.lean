import Mathlib

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 2, Sect. 2: a (finite) congestion game `(N, E, (Σᵢ)_{i∈N}, (f_e)_{e∈E})` on players `ι` and
facilities `E`.

**Formalization Note.** The printed tuple indexes the latencies by `e ∈ M` and calls `f_e` the latency
"associated with facility j"; both are misprints for `e ∈ E`, facility `e`. Latencies are real-valued
functions of the (natural-number) number of users. -/
structure CongestionGame (ι : Type*) (E : Type*) where
  /-- `Σᵢ ⊆ 2^E`: the pure strategies of player `i`, each a set of facilities. -/
  strategies : ι → Finset (Finset E)
  /-- `f_e`: the latency (cost) of facility `e` as a function of its number of users. -/
  latency : E → ℕ → ℝ

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- `n_e(A)` (Sect. 2, PDF p. 2): the number of players using facility `e` in the profile `A`. -/
def load (A : ι → Finset E) (e : E) : ℕ := (Finset.univ.filter (fun i => e ∈ A i)).card

/-- The cost of player `i` in the profile `A` (Sect. 2, PDF p. 2):
`cᵢ(A) = Σ_{e∈Aᵢ} f_e(n_e(A))`. -/
noncomputable def cost (G : CongestionGame ι E) (A : ι → Finset E) (i : ι) : ℝ :=
  ∑ e ∈ A i, G.latency e (load A e)

/-- `A` is a pure strategy profile of `G` (Sect. 2, PDF p. 2): `Aᵢ ∈ Σᵢ` for every player `i`. -/
def IsProfile (G : CongestionGame ι E) (A : ι → Finset E) : Prop := ∀ i, A i ∈ G.strategies i

/-- Pure Nash equilibrium (Sect. 2, PDF p. 2): `A` is a pure strategy profile and
`∀ i ∈ N, ∀ S ∈ Σᵢ, cᵢ(A) ≤ cᵢ(A₋ᵢ, S)`, where `(A₋ᵢ, S)` is `A` with `Aᵢ` replaced by `S`.

**Formalization Note.** This is the cost form of the paper; it is the same notion as the payoff-form
`AGT.IsPureNash` of `agt_games` with strategy types `↥(G.strategies i)` and payoffs `u i A = −cᵢ(A)`. -/
def IsPureNash (G : CongestionGame ι E) (A : ι → Finset E) : Prop :=
  IsProfile G A ∧ ∀ i, ∀ S ∈ G.strategies i, cost G A i ≤ cost G (Function.update A i S) i

/-- The social cost `SUM(A) = Σ_{i∈N} cᵢ(A)` (Sect. 2, PDF p. 2): the sum of the players' costs,
`N` times the average social cost. -/
noncomputable def sumCost (G : CongestionGame ι E) (A : ι → Finset E) : ℝ := ∑ i, cost G A i

/-- The maximum social cost `MAX(A) = max_{i∈N} cᵢ(A)` (Sect. 2, PDF p. 2). It needs at least one
player, hence the `Nonempty ι` instance. -/
noncomputable def maxCost [Nonempty ι] (G : CongestionGame ι E) (A : ι → Finset E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (cost G A)

/-- Linear latencies (Sect. 2, PDF p. 2; §1.1, PDF p. 1): every facility has a latency
`f_e(k) = a_e·k + b_e` with nonnegative constants `a_e` and `b_e`. -/
def IsLinear (G : CongestionGame ι E) : Prop :=
  ∃ a b : E → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ e, 0 ≤ b e) ∧ ∀ e k, G.latency e k = a e * k + b e

/-- Symmetric (single-commodity) congestion game (Sect. 2, PDF p. 2): all the players have the same
strategy set, `Σᵢ = Σ`. -/
def IsSymmetric (G : CongestionGame ι E) : Prop := ∀ i j, G.strategies i = G.strategies j

end CongestionPoA.SymMax
