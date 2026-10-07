import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

/-- Talagrand (1995), p. 124, Lemma 4.1.2: for `t ≥ 0`, `x ∈ A_t^c` (Eq. (4.1.4)) iff for every
real family `(α_i)_{i ≤ N}` there is `y ∈ A` with
`Σ { α_i ; x_i ≠ y_i } ≤ t (Σ_i α_i²)^{1/2}` (Eq. (4.1.5)). -/
theorem lemma_4_1_2 {Ω : Type*} [DecidableEq Ω] {N : ℕ} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) (t : ℝ) (ht : 0 ≤ t) :
    x ∈ enlarge A t ↔
      ∀ a : Fin N → ℝ, ∃ y ∈ A,
        (∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), a i) ≤ t * Real.sqrt (∑ i, a i ^ 2) := by sorry

end TalagrandConc.ConvexHull

