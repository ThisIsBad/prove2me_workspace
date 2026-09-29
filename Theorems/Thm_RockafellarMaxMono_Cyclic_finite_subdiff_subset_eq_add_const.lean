import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff

namespace RockafellarMaxMono.Cyclic

theorem finite_subdiff_subset_eq_add_const {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (h k : V → ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (kconv : ConvexOn ℝ Set.univ k) (kcont : Continuous k)
    (hsub : ∀ x : V, Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x ⊆
      Shared.subdiff (fun y => ((k y : ℝ) : EReal)) x) :
    ∃ c : ℝ, ∀ x : V, k x = h x + c := by sorry

end RockafellarMaxMono.Cyclic

