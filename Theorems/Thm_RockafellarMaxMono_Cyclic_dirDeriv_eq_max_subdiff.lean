import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
open Filter Topology

namespace RockafellarMaxMono.Cyclic

theorem dirDeriv_eq_max_subdiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (x : V) :
    (Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x).Nonempty ∧
    IsCompact (StrongDual.toWeakDual '' Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) ∧
    ∀ u : V, ∃ d : ℝ,
      Tendsto (fun t : ℝ => (h (x + t • u) - h x) / t) (𝓝[>] 0) (𝓝 d) ∧
      IsGreatest ((fun x' : StrongDual ℝ V => x' u) ''
        Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) d := by sorry

end RockafellarMaxMono.Cyclic

