import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_AgreeTmax_FBEDD

namespace BurnInBatch.AgreeTmax

/-- Algorithm FBEDD optimally solves `1/p_i = p, B/T_max` (Lee, Uzsoy & Martin-Vega 1992,
p. 769): if every job has processing time `c` and the jobs are indexed in nondecreasing order of
due dates, the full-batch EDD schedule is a valid batch schedule of all jobs, and its maximum
tardiness is at most that of every valid batch schedule of all jobs. -/
theorem fbedd_optimal {n B : ℕ} (hB : 0 < B) (c : ℕ) (d : Fin n → ℕ) (hd : Monotone d) :
    IsValid B Finset.univ (fbedd n B) ∧
      ∀ S : List (Finset (Fin n)), IsValid B Finset.univ S →
        Tmax (fun _ => c) d (fbedd n B) ≤ Tmax (fun _ => c) d S := by sorry

end BurnInBatch.AgreeTmax

