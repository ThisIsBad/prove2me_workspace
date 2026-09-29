import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

open scoped ENNReal

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): a request to a stale vertex (requested in the previous
phase, not yet in this phase) is a fault with probability `c/s`, where `c` is the number of
clean vertices requested in the phase so far and `s` the current number of stale vertices. -/
theorem stale_fault_prob {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (i t : ℕ) (ht : t < σ.length)
    (hi : IsPhaseStart k (initVertices e hkn) σ i) (hit : i ≤ t)
    (hno : ∀ u, i < u → u ≤ t → ¬ IsPhaseStart k (initVertices e hkn) σ u)
    (hstale : σ.get ⟨t, ht⟩ ∈ marksAt k (initVertices e hkn) σ i)
    (hnew : σ.get ⟨t, ht⟩ ∉ phaseRequested σ i t) :
    faultProb k (initVertices e hkn) (σ.take t) (σ.get ⟨t, ht⟩) =
      ((phaseRequested σ i t \ marksAt k (initVertices e hkn) σ i).card : ℝ≥0∞)
        / ((marksAt k (initVertices e hkn) σ i \ phaseRequested σ i t).card : ℝ≥0∞) := by sorry

end CompetitivePaging.Marking
