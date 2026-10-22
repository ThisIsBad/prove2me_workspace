import Mathlib
import Definitions.Def_agt_games

namespace WorstCaseEq.Identical

/-!
The load-balancing game of Koutsoupias & Papadimitriou, *Worst-case equilibria* (journal version, 2009),
*The model* (PDF p. 2), §2 (PDF pp. 3–4) and the proof of Theorem 3 (PDF p. 5): `n` agents with traffic
`w i` each choose one of `m` identical parallel links. Agents are `Fin n`, links are `Fin m` (the paper's
agents and links are numbered from 1, here from 0). A mixed profile is `p : Fin n → Fin m → ℝ`, with
`p i j` the probability `p_i^j` that agent `i` picks link `j`. The game is encoded on top of the published
`agt_games` vocabulary, which maximizes payoffs, so the payoff of an agent is minus its cost.
-/

noncomputable section

variable {n m : ℕ}

/-- The traffic on link `j` under the pure profile `s` (agent `k` on link `s k`):
`∑_{k : j_k = j} w_k`. -/
def load (w : Fin n → ℝ) (s : Fin n → Fin m) (j : Fin m) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => s k = j), w k

/-- The payoff of agent `i` in the pure profile `s`: minus its cost `c_i = ∑_{k : j_k = j_i} w_k`,
the traffic on the link agent `i` chose (PDF p. 2). -/
def payoff (w : Fin n → ℝ) : Fin n → (Fin n → Fin m) → ℝ :=
  fun i s => -load w s (s i)

/-- A (mixed) Nash equilibrium of the game: `p` is a profile of lotteries over the links from which no
agent can lower its expected cost by switching unilaterally to any other lottery (PDF pp. 2–3). -/
def IsNash (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) : Prop :=
  AGT.IsMixedNash (S := fun _ : Fin n => Fin m) (payoff w) p

/-- The expected cost `c_i` of agent `i` under the mixed profile `p`: the expected traffic on the link
agent `i` chooses, links being chosen independently with the probabilities `p` (PDF p. 2). -/
def expCost (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  -AGT.expectedPayoff (S := fun _ : Fin n => Fin m) (payoff w) p i

/-- The expected traffic `M^j = ∑_i p_i^j w_i` on link `j`, (1) (PDF p. 3). -/
def expTraffic (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ i, p i j * w i

/-- The cost `c_i^j = w_i + ∑_{k ≠ i} p_k^j w_k` of agent `i` when its own traffic is assigned to link
`j`, first form of (2) (PDF p. 3). -/
def linkCost (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  w i + ∑ k ∈ Finset.univ.erase i, p k j * w k

/-- The pure strategy "link `j`" as a lottery: probability `1` on `j`, `0` elsewhere. -/
def pureLottery (j : Fin m) : Fin m → ℝ :=
  fun j' => if j' = j then 1 else 0

/-- The collision probability `t_ik = ∑_j p_i^j p_k^j` of agents `i` and `k` (proof of Theorem 3,
PDF p. 5). -/
def collisionProb (p : Fin n → Fin m → ℝ) (i k : Fin n) : ℝ :=
  ∑ j, p i j * p k j

section Links

variable [NeZero m]

/-- The maximum traffic `max_{j} ∑_{k : j_k = j} w_k` over all links under the pure profile `s`
(the makespan of the assignment `s`). -/
def makespan (w : Fin n → ℝ) (s : Fin n → Fin m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (load w s)

/-- The social cost (4) (PDF p. 4): the expected maximum traffic over all links,
`∑_{j_1} ⋯ ∑_{j_n} ∏_i p_i^{j_i} · max_j ∑_{k : j_k = j} w_k`. -/
def socialCost (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) : ℝ :=
  ∑ s : Fin n → Fin m, AGT.profileProb (S := fun _ : Fin n => Fin m) p s * makespan w s

/-- The social optimum `opt`: the optimum of the `m`-way load balancing problem, i.e. the least makespan
over all pure assignments of the `n` agents to the `m` links (PDF p. 2). The number of links `m` is an
explicit argument, since `w` does not determine it. -/
def opt (m : ℕ) [NeZero m] (w : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (makespan (m := m) w)

/-- Link `j` is the lexicographically first link of maximum load under the pure profile `s`
(proof of Theorem 3, PDF p. 5). -/
def IsFirstMaxLink (w : Fin n → ℝ) (s : Fin n → Fin m) (j : Fin m) : Prop :=
  load w s j = makespan w s ∧ ∀ j', j' < j → load w s j' < makespan w s

open Classical in
/-- The contribution probability `q_i` of agent `i`: the probability that its traffic goes to the
(lexicographically first) link of maximum load (proof of Theorem 3, PDF p. 5). -/
def contribProb (w : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ s : Fin n → Fin m, AGT.profileProb (S := fun _ : Fin n => Fin m) p s *
    (if IsFirstMaxLink w s (s i) then 1 else 0)

end Links

end

end WorstCaseEq.Identical
