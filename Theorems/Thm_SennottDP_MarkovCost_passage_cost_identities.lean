import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

/-- Sennott (1999), Proposition C.2.2, p. 299. Let `G` be a nonempty subset of `S`.
(i) If `m_{iG} < ∞`, then `c_{iG} = ∑_k C(k) _G u_{ik}`.
(ii) Under the hypothesis of (i), (C.13) `c_{iG} = C(i) + ∑_{j ∉ G} P_{ij} c_{jG}`.
(iii) If `G` is contained in a positive recurrent class `R`, then `J_R = ∑_{i ∈ G} π_i c_{iG}`.
(iv) If `R` is a positive recurrent class with `J_R < ∞`, then `c_{ij} < ∞` for all `i, j ∈ R`. -/
theorem passage_cost_identities {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = ∑' k, (C k : ℝ≥0∞) * visits M G i k) ∧
    (∀ i, meanPassage M G i < ⊤ →
      passageCost M C G i = (C i : ℝ≥0∞) + ∑' j : ↥Gᶜ, M.P i j * passageCost M C G j) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      classAvgCost M C R = ∑' i : G, steadyState M i * passageCost M C G i) ∧
    (∀ R : Set S, IsPosRecClass M R → classAvgCost M C R < ⊤ →
      ∀ i ∈ R, ∀ j ∈ R, passageCost M C {j} i < ⊤) := by sorry

end SennottDP.MarkovCost

