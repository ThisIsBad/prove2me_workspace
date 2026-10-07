import Mathlib
import Definitions.Def_FlowJobShop_PairGroups_FlowShop
import Definitions.Def_FlowJobShop_PairGroups_AlgorithmH

namespace FlowJobShop.PairGroups

open FlowShop

/-- Proof of Lemma 11 (p. 49): the finish time of an optimal schedule of the flow shop on any
processor group is at most the finish time of any feasible schedule of the whole flow shop;
hence `FT(S*) ≥ max_g f(R(g))`. -/
theorem group_optimum_le_finishTime {m n : ℕ} (F : FlowShop m n)
    (R : (g : Fin ((m + 1) / 2)) → Fin (groupSize m g) → Fin n → ℝ)
    (hR : ∀ g, (F.group g).IsOptimal (R g))
    (τ : Fin m → Fin n → ℝ) (hτ : F.IsFeasible τ) :
    (Finset.univ : Finset (Fin ((m + 1) / 2))).fold max 0
        (fun g => (F.group g).finishTime (R g)) ≤ F.finishTime τ := by sorry

end FlowJobShop.PairGroups

