import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_class_convergence_equivalences {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) (R : Set S) (hR : Γ.IsPosRecClass R) :
    List.TFAE
      [∀ i ∈ R, Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i)),
       ∃ z ∈ R, Tendsto (fun N => AS.meanPassageN {z} N z) atTop
         (𝓝 (Γ.meanPassage {z} z)),
       ∀ G : Finset S, G.Nonempty → (↑G : Set S) ⊆ R → ∀ i ∈ R,
         Tendsto (fun N => AS.meanPassageN (↑G : Set S) N i) atTop
           (𝓝 (Γ.meanPassage (↑G : Set S) i))] ∧
    ((∀ i ∈ R, Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i))) →
      List.TFAE
        [∀ i ∈ R, Tendsto (fun N => AS.avgCostN N i) atTop (𝓝 (Γ.classAvgCost R)),
         ∃ z ∈ R, Tendsto (fun N => AS.passageCostN {z} N z) atTop
           (𝓝 (Γ.passageCost {z} z)),
         ∀ G : Finset S, G.Nonempty → (↑G : Set S) ⊆ R → ∀ i ∈ R,
           Tendsto (fun N => AS.passageCostN (↑G : Set S) N i) atTop
             (𝓝 (Γ.passageCost (↑G : Set S) i))]) := by sorry

end SennottDP.ChainASM

