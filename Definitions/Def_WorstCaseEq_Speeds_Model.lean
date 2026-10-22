import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Identical_Model

noncomputable section

namespace WorstCaseEq.Speeds

/-!
Load balancing on `m` parallel links with speeds (Koutsoupias & Papadimitriou, *Worst-case
equilibria*, journal version 2009: *The model*, PDF p. 2; §2, PDF p. 3; (4), PDF p. 4;
§3 *Links with different capacities*, (8), PDF p. 6).

Agents `Fin n` with traffic `w i`, links `Fin m` with speeds `s j`.  A pure profile
`a : Fin n → Fin m` sends agent `i` to link `a i`; an agent on link `j` carrying total traffic `L`
experiences delay `L / s j`.  A mixed profile `p : Fin n → Fin m → ℝ` gives `p i j = p_i^j`, the
probability that agent `i` picks link `j`.  The game is cast in the payoff-maximizing convention of
`agt_games`: the payoff is minus the delay.
-/

variable {n m : ℕ}

/-- The payoff of agent `i` under the pure profile `a`: minus its delay `load w a (a i) / s (a i)`,
the traffic on its link divided by the link's speed (*The model*, PDF p. 2, with speeds as in §3,
PDF p. 6). -/
def payoff (w : Fin n → ℝ) (s : Fin m → ℝ) : Fin n → (Fin n → Fin m) → ℝ :=
  fun i a => -(WorstCaseEq.Identical.load w a (a i) / s (a i))

/-- `p` is a (mixed) Nash equilibrium of the game with traffic `w` and speeds `s`: a profile of
lotteries from which no agent can lower its expected delay by switching to any other lottery. -/
def IsNash (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) : Prop :=
  AGT.IsMixedNash (payoff w s) p

/-- The expected cost (expected delay) `c_i` of agent `i` under the mixed profile `p`. -/
def expCost (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  -AGT.expectedPayoff (payoff w s) p i

/-- The cost `c_i^j = (w_i + ∑_{k ≠ i} p_k^j w_k) / s_j` to agent `i` of assigning its traffic to
link `j` ((2), PDF p. 3, divided by the speed as in (8), PDF p. 6). -/
def linkCost (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  (w i + ∑ k ∈ Finset.univ.erase i, p k j * w k) / s j

section NeZero

variable [NeZero m]

/-- The makespan of the pure profile `a`: the largest delay `load w a j / s j` over the links. -/
def makespan (w : Fin n → ℝ) (s : Fin m → ℝ) (a : Fin n → Fin m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => WorstCaseEq.Identical.load w a j / s j)

/-- The social cost of the mixed profile `p` ((4), PDF p. 4, with speeds): the expected makespan
over the product distribution, `∑_a (∏_i p_i^{a_i}) · max_j load_j(a) / s_j`. -/
def socialCost (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ) : ℝ :=
  ∑ a : Fin n → Fin m, AGT.profileProb p a * makespan w s a

/-- The optimum `opt`: the least makespan over all pure assignments of the agents to the links. -/
def opt (w : Fin n → ℝ) (s : Fin m → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (makespan w s)

end NeZero

/-- The speeds `(s₁, s₂)` of the two links of Theorem 4 (links 1, 2 of the paper are `0, 1`). -/
def speeds (s₁ s₂ : ℝ) : Fin 2 → ℝ := ![s₁, s₂]

/-- The traffic of the two agents in the proof of Theorem 4, PDF p. 6: `w₁ = s₂`, `w₂ = s₁`
(agents 1, 2 of the paper are `0, 1`). -/
def instWeights (s₁ s₂ : ℝ) : Fin 2 → ℝ := ![s₂, s₁]

/-- The mixed profile in the proof of Theorem 4, PDF p. 6 (row = agent, column = link):
`p₁¹ = s₁²/(s₂(s₁+s₂))`, `p₂¹ = 1 − s₂²/(s₁(s₁+s₂))`, and `p_i² = 1 − p_i¹`. -/
def instProfile (s₁ s₂ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![s₁ ^ 2 / (s₂ * (s₁ + s₂)), 1 - s₁ ^ 2 / (s₂ * (s₁ + s₂))],
    ![1 - s₂ ^ 2 / (s₁ * (s₁ + s₂)), s₂ ^ 2 / (s₁ * (s₁ + s₂))]]

end WorstCaseEq.Speeds

end
