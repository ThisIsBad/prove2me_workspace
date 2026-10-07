import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Computational procedure, pp. 572–575. For symmetric distances,
`C₁ < ⋯ < C_n`, `x₁ = ∞`, and an initial allocation of one truck per customer that passes the
Table II test:
1. every run of the procedure is finite (whatever the tie-breaks);
2. a reachable state from which some cell is admissible always has a successor;
3. every final state is an allocation of the customers that the available trucks can carry;
4. every final state satisfies relation (A);
5. the mileage of every final state is `2 ∑_j d_{0,j}` less the savings of the linked cells
   `(y:z)`, `y < z`. -/
theorem savings_procedure_correct {M n : ℕ} (I : Instance M n)
    (hsymm : ∀ i j, I.d i j = I.d j i) (hC : StrictMono I.C) (hx : I.x 0 = ⊤)
    (hinit : I.TableIIOK ↑((init M).map I.runLoad)) :
    Acc (fun s' s => Step I s s') (init M) ∧
    (∀ s : State M, Reachable I s → ¬ Terminal I s → ∃ s', Step I s s') ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad)) ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      ∀ y : Fin (M + 1), y ≠ 0 → ∑ z ∈ Finset.univ.erase y, t s y z = 2) ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      I.mileage s = ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), 2 * I.d 0 j -
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
            (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t s p.1 p.2 = 1),
          I.saving p.1 p.2) := by sorry

end ClarkeWright64.Savings

