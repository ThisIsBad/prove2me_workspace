import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- §5, proof of Theorem 7, p. 9 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987)): "no
schedule with makespan pq can have idle time, and … each machine processes either q element jobs
of length p or p dummy jobs of length q". For `0 < p < q` relatively prime and any schedule `σ`
of the instance `twoTimes p q n S` with makespan at most `p * q`:
1. every machine has load exactly `p * q`;
2. every element job runs on a machine whose tuple contains its element (so it has length `p`);
3. every machine processes either exactly `q` element jobs and no dummy job, or no element job
   and exactly `p` dummy jobs. -/
theorem no_idle_two_kinds {p q m n : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (S : Fin m → Finset (Fin (q * n))) (σ : Fin (q * n + p * (m - n)) → Fin m)
    (hσ : makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ)) :
    (∀ i : Fin m, load (fun i j => (twoTimes p q n S i j : ℝ)) σ i = (p * q : ℝ)) ∧
      (∀ u : Fin (q * n), u ∈ S (σ (elemJob p q n m u))) ∧
      (∀ i : Fin m,
        ((Finset.univ.filter (fun u => σ (elemJob p q n m u) = i)).card = q ∧
            ∀ k : Fin (p * (m - n)), σ (dummyJob p q n m k) ≠ i) ∨
          ((∀ u : Fin (q * n), σ (elemJob p q n m u) ≠ i) ∧
            (Finset.univ.filter (fun k => σ (dummyJob p q n m k) = i)).card = p)) := by sorry

end UnrelatedSched.TwoTimes

