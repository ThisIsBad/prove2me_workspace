import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): in a complete phase, a lazy adversary's cost `C_A`
satisfies `C_A ≥ max(l - d, d') ≥ (l - d + d')/2`. -/
theorem adversary_phase_cost_ge_half {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
        ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) ∧
      (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
          + ((Finset.univ.filter
              (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)) / 2
        ≤ max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ) := by sorry

end CompetitivePaging.Marking

