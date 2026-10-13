import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.ThreeHalves

/-- Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), §4, Corollary 2, p. 8 (the content of its
proof): let `ρ < 3/2` and let `σ` be a schedule of the instance of Theorem 5 built from the
3-dimensional matching instance `T` that is within the factor `ρ` of every schedule of that
instance. Then `σ` has makespan at most `2` if and only if `T` has a matching; so the output of
any `ρ`-approximation algorithm on this instance decides 3-DIMENSIONAL MATCHING. -/
theorem corollary_2 {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (ρ : ℝ) (hρ : ρ < 3 / 2)
    (σ : Fin (numJobs T) → Fin m)
    (hσ : ∀ τ : Fin (numJobs T) → Fin m,
      makespan (fun i r => (P T i r : ℝ)) σ ≤ ρ * makespan (fun i r => (P T i r : ℝ)) τ) :
    makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 ↔ HasMatching T := by sorry

end UnrelatedSched.ThreeHalves

