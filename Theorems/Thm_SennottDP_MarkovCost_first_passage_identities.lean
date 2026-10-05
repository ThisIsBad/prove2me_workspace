import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost

open Classical in
/-- Sennott (1999), Proposition C.1.4, pp. 295–296. Let `G` be a nonempty subset of `S`.
(i) For `k ∉ G`, `_G u_{ik} = δ_{ik} + ∑_{t ≥ 1} _G P^{(t)}_{ik}`.
(ii) `m_{iG} = ∑_{k ∈ S} _G u_{ik}`.
(iii) (C.2) `_G P^{(t+1)}_{ik} = ∑_{j ∉ G} P_{ij} _G P^{(t)}_{jk}` for `i, k ∈ S`, `t ≥ 1`;
(C.3) `_G u_{ik} = δ_{ik} + ∑_{j ∉ G} P_{ij} _G u_{jk}` for `i, k ∈ S`;
(C.4) `m_{iG} = 1 + ∑_{j ∉ G} P_{ij} m_{jG}` for `i ∈ S`.
(iv) If `G` is contained in a positive recurrent class `R`, then `π_j = ∑_{i ∈ G} π_i _G u_{ij}` for
`j ∈ R` and `∑_{i ∈ G} π_i m_{iG} = 1`.
(v) If `R` is a positive recurrent class, then `m_{ij} < ∞` for all `i, j ∈ R`. -/
theorem first_passage_identities {S : Type} [Countable S] (M : MC S) (G : Set S)
    (hG : G.Nonempty) :
    (∀ i, ∀ k ∉ G,
      visits M G i k = (if i = k then 1 else 0) + ∑' t : ℕ, taboo M G (t + 1) i k) ∧
    (∀ i, meanPassage M G i = ∑' k, visits M G i k) ∧
    ((∀ i k, ∀ t : ℕ, 1 ≤ t →
        taboo M G (t + 1) i k = ∑' j : ↥Gᶜ, M.P i j * taboo M G t j k) ∧
      (∀ i k, visits M G i k = (if i = k then 1 else 0) + ∑' j : ↥Gᶜ, M.P i j * visits M G j k) ∧
      (∀ i, meanPassage M G i = 1 + ∑' j : ↥Gᶜ, M.P i j * meanPassage M G j)) ∧
    (∀ R : Set S, IsPosRecClass M R → G ⊆ R →
      (∀ j ∈ R, steadyState M j = ∑' i : G, steadyState M i * visits M G i j) ∧
      ∑' i : G, steadyState M i * meanPassage M G i = 1) ∧
    (∀ R : Set S, IsPosRecClass M R → ∀ i ∈ R, ∀ j ∈ R, meanPassage M {j} i < ⊤) := by sorry

end SennottDP.MarkovCost

