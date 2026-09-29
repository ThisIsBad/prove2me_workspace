import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): at the start of every phase the marked vertices are
precisely the ones occupied by the marking algorithm's servers, and the first request of the
phase is to an unmarked vertex. -/
theorem phase_start_marked_eq_covered {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (t : ℕ) (ht : t < σ.length)
    (hstart : IsPhaseStart k (initVertices e hkn) σ t) :
    ∀ s ∈ (lawAfter k (initVertices e hkn) (σ.take t)).support,
      s.marked = s.covered ∧ σ.get ⟨t, ht⟩ ∉ s.marked := by sorry

end CompetitivePaging.Marking
