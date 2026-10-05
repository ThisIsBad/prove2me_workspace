import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Shapley (fair) cost sharing (Anshelevich et al., SIAM J. Comput. 38 (2008), Sect. 2 and
Theorem 2.1, proof, p. 1607 (PDF p. 6); Theorem 2.3, p. 1608 (PDF p. 7)): the congestion game with
strategy families `strategies` in which every one of the `x` users of edge `e` pays `c_e(x)/x`,
where `c_e(x)` is the cost of building `e` for `x` users. For the constant costs of Theorem 2.1
take `c e x = c_e`.

**Formalization Note.** Strategy families are arbitrary families of edge sets (the paper's
*Extensions* paragraph, p. 1609: the proofs "did not rely on the graph structure"); the fair
connection game on a directed graph is the instance `Σᵢ = {S ⊆ E : S connects Tᵢ}`. Lean's
`c / 0 = 0` is only reached for an edge nobody uses, which no player cost ever sums over. -/
noncomputable def fairGame (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) :
    CongestionGame ι E :=
  ⟨strategies, fun e x => c e x / x⟩

/-- The total cost of the designed network (Sect. 1, p. 1603 (PDF p. 2); Sect. 2, p. 1607):
`cost(S) = Σ_{e ∈ ∪ᵢ Sᵢ} c_e(x_e)`, the cost of the edges that at least one player uses, each
built for its number of users `x_e`. Unused edges cost nothing. -/
noncomputable def designCost (c : E → ℕ → ℝ) (S : ι → Finset E) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => 0 < load S e), c e (load S e)

/-- Rosenthal's potential (2.1) (Theorem 2.1, proof, p. 1607 (PDF p. 6)):
`Φ(S) = Σ_{e∈E} Σ_{x=1}^{x_e} f_e(x)`, where `f_e` is the per-user cost (latency) of edge `e`. -/
noncomputable def potential (G : CongestionGame ι E) (S : ι → Finset E) : ℝ :=
  ∑ e, ∑ x ∈ Finset.Icc 1 (load S e), G.latency e x

/-- The cost hypotheses of Theorem 2.3 (p. 1608 (PDF p. 7)): every edge cost `c_e(x)`, as a
function of the number `x ∈ ℕ` of users, is nondecreasing and (discretely) concave, i.e. its
increments `c_e(x+1) − c_e(x)` are nonincreasing, and `c_e(0) ≥ 0`.

**Formalization Note.** Concavity is stated on `ℕ` (the number of users), as nonincreasing
increments. The condition `c_e(0) ≥ 0` is implicit in the paper: its claim that the cost per player
`c_e(x)/x` decreases for concave `c_e` needs it (`c(x) = 2x − 1` is concave and nondecreasing, but
`c(x)/x` increases). `c_e(0)` is never charged, since unused edges cost nothing. -/
def IsConcaveCost (c : E → ℕ → ℝ) : Prop :=
  ∀ e, 0 ≤ c e 0 ∧ Monotone (c e) ∧ ∀ x, c e (x + 2) - c e (x + 1) ≤ c e (x + 1) - c e x

end PriceOfStability.Harmonic
