import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): in a complete phase, a lazy adversary `A` pays at least
`l - d`, where `l` is the number of clean vertices requested in the phase and `d` is the
number of `A`'s servers outside the marking algorithm's servers (= the marked set) at the
start of the phase. -/
theorem adversary_cost_ge_clean_sub_d {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
        - ((Finset.univ.filter
            (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
      ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by sorry

end CompetitivePaging.Marking
