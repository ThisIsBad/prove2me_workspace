import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (pp. 4–5): in a complete phase with `l` requests to clean vertices,
the expected cost of the marking algorithm is at most `l (H_k - H_l + 1) ≤ l H_k`. -/
theorem phase_expected_cost_le {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    markingPhaseCost k (initVertices e hkn) σ i i'
        ≤ ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * ((harmonic k : ℝ)
            - (harmonic (phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
            + 1) ∧
      ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * ((harmonic k : ℝ)
            - (harmonic (phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
            + 1)
        ≤ ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * (harmonic k : ℝ) := by sorry

end CompetitivePaging.Marking
