import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_passage_cost_liminf {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (G : Finset S) (hG : G.Nonempty) (i : S)
    (hm : Γ.meanPassage (↑G : Set S) i < ⊤)
    (hmN : ∀ᶠ N in atTop, AS.meanPassageN (↑G : Set S) N i < ⊤) :
    Γ.passageCost (↑G : Set S) i ≤
      liminf (fun N => AS.passageCostN (↑G : Set S) N i) atTop := by sorry

end SennottDP.ChainASM

