import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.Mixed

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- The payoff function of the congestion game `G` as a game in the sense of `agt_games`
(Sect. 2, PDF p. 2): player `i`'s pure strategies are the elements of `Σᵢ` (the finite type
`↥(G.strategies i)`), and on the pure profile `s` player `i` receives `−cᵢ(s)`, the negative of their
cost on the profile of facility sets `j ↦ s_j`.

**Formalization Note.** `agt_games` is payoff-maximizing; the paper's players minimize cost. The sign
flip makes the two conventions agree. -/
noncomputable def payoff (G : CongestionPoA.AsymSum.CongestionGame ι E) :
    ι → (∀ i, ↥(G.strategies i)) → ℝ :=
  fun i s => -CongestionPoA.AsymSum.cost G (fun j => (s j).1) i

/-- Mixed Nash equilibrium of a congestion game (Sect. 2, PDF p. 2: "A *mixed* strategy pᵢ for a
player i, is a probability distribution over his pure strategy set Σᵢ. The above definitions extend
naturally to this case (with expected costs, of course)"): `σ` assigns to each player `i` a probability
distribution `σ i` on `Σᵢ`, the players randomize independently, and no player can lower their
expected cost by switching unilaterally to another probability distribution on `Σᵢ`.

**Formalization Note.** This is `AGT.IsMixedNash` of `agt_games` applied to `payoff G`; lowering the
expected cost is raising the expected payoff `−cost`. Deviations range over all lotteries, which is
equivalent to deviations to pure strategies (a point mass is a lottery, and an expected payoff is
linear in the deviating player's lottery). -/
def IsMixedNash (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) : Prop :=
  AGT.IsMixedNash (payoff G) σ

/-- The expected cost `E[cᵢ]` of player `i` under the mixed profile `σ` (Sect. 2, PDF p. 2, "with
expected costs"; Sect. 5, PDF p. 6): the expectation of `cᵢ(s)` when the pure profile `s` is drawn
from the product distribution `Prob(s) = Πⱼ σⱼ(sⱼ)`.

**Formalization Note.** This is the expected value of the cost, not the cost of an averaged profile;
it equals `−AGT.expectedPayoff (payoff G) σ i`. -/
noncomputable def expCost (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) (i : ι) : ℝ :=
  ∑ s : ∀ j, ↥(G.strategies j), AGT.profileProb σ s * CongestionPoA.AsymSum.cost G (fun j => (s j).1) i

/-- The expected load `E[n_e]` of facility `e` under the mixed profile `σ`: the expected number of
players using `e` when the pure profile is drawn from `Prob(s) = Πⱼ σⱼ(sⱼ)`. -/
noncomputable def expLoad (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) (e : E) : ℝ :=
  ∑ s : ∀ j, ↥(G.strategies j), AGT.profileProb σ s * (CongestionPoA.AsymSum.load (fun j => (s j).1) e : ℝ)

/-- The social cost of a mixed profile (Sect. 5, PDF p. 6): "the average (or sum) of the expected cost
of all players SUM = Σ_{i∈N} cᵢ(N)", i.e. `Σᵢ E[cᵢ]`.

**Formalization Note.** The printed argument "`cᵢ(N)`" stands for the expected cost of player `i`
under the mixed profile. The paper's second option, `Σ_e E[n_e²]`, is not this definition. -/
noncomputable def mixedSumCost (G : CongestionPoA.AsymSum.CongestionGame ι E) (σ : ∀ i, ↥(G.strategies i) → ℝ) : ℝ :=
  ∑ i, expCost G σ i

end CongestionPoA.Mixed
