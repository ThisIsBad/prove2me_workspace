import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_taboo_visits_passage_limits {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (G : Finset S) (hG : G.Nonempty) :
    (∀ i k : S, ∀ t : ℕ, 1 ≤ t →
      Tendsto (fun N => AS.tabooProbN (↑G : Set S) t N i k) atTop
        (𝓝 (Γ.tabooProb (↑G : Set S) t i k))) ∧
    (∀ k ∈ G, ∀ i : S, Γ.visits (↑G : Set S) i k = (if i = k then 1 else 0) ∧
      ∀ᶠ N in atTop, AS.visitsN (↑G : Set S) N i k = Γ.visits (↑G : Set S) i k) ∧
    (∀ i k : S, Γ.visits (↑G : Set S) i k ≤
      liminf (fun N => AS.visitsN (↑G : Set S) N i k) atTop) ∧
    (∀ i : S, Γ.meanPassage (↑G : Set S) i ≤
      liminf (fun N => AS.meanPassageN (↑G : Set S) N i) atTop) := by sorry

end SennottDP.ChainASM

