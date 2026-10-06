import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Appendix, proof of Property IV(G), the two optimality conditions (Baker and Scudder 1990,
p. 35), as sufficient conditions. For the job in 0-based position `k`:
(1) if `∑_{i<k} α_i < ∑_{i≥k} β_i` and `∑_{i<k} α_i ≥ ∑_{i>k} β_i`, then `d = C_k - v_k` is the
least optimal due date;
(2) if `∑_{i<k} α_i < ∑_{i>k} β_i` and `∑_{i≤k} α_i ≥ ∑_{i>k} β_i`, then `d = C_k + u_k` is the
least optimal due date. -/
theorem optimality_conditions {n : ℕ} (I : Instance n) (k : Fin n) :
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), I.β i) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) →
      I.IsLeastOptimalDueDate (I.C k - I.v k)) ∧
    ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), I.α i) →
      I.IsLeastOptimalDueDate (I.C k + I.u k)) := by sorry

end BakerScudder1990.Tolerance

