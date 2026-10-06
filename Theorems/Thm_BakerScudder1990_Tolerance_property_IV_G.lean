import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Property IV(G) (Baker and Scudder 1990, p. 30), with the case labels as derived in its proof
(p. 35); the printed statement swaps them. For a fixed sequence of `n > 0` jobs processed without
inserted idle time, a least optimal common due date exists; at every least optimal due date `d`,
let `b = k + 1` be the number of jobs with zero tardiness `(C_j - d - v_j)^+ = 0`. Then either
`C_k = d + v_k` with `∑_{i<k} α_i < ∑_{i≥k} β_i` and `∑_{i<k} α_i ≥ ∑_{i>k} β_i`, or
`C_k = d - u_k` with `∑_{i<k} α_i < ∑_{i>k} β_i` and `∑_{i≤k} α_i ≥ ∑_{i>k} β_i`.
Positions are 0-based: the paper's job `b` is position `k` with `b = k + 1`. -/
theorem property_IV_G {n : ℕ} (I : Instance n) (hn : 0 < n) :
    (∃ d : ℝ, I.IsLeastOptimalDueDate d) ∧
      ∀ d : ℝ, I.IsLeastOptimalDueDate d →
        ∃ k : Fin n,
          (Finset.univ.filter (fun j : Fin n => I.tardiness d j = 0)).card = k.val + 1 ∧
          ((I.C k = d + I.v k ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i), I.β i) ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i)) ∨
           (I.C k = d - I.u k ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < k), I.α i) <
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ∧
              (∑ i ∈ Finset.univ.filter (fun i : Fin n => k < i), I.β i) ≤
                (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), I.α i))) := by sorry

end BakerScudder1990.Tolerance

