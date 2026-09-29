import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

/-- **Theorem 6.1 = Theorem 1.2** (Borodin–Linial–Saks 1992, pp. 755 and 747). For any task
system `(S, d)` with `n ≥ 2` states (not necessarily symmetric), the continuous-time on-line
algorithm `A*_d` (with any tie-breaking, given for each initial state `s₀` by a state sequence
`seq s₀` satisfying `IsAstarSeq`) has competitive ratio at most `(2n − 1) ψ(d)`: for every
`w > (2n − 1) ψ(d)` there is a constant `K` with `c_{A*_d}(T) ≤ w · c₀(T) + K` for every
finite nonnegative task sequence `T` and every initial state `s₀`. -/
theorem astar_competitive {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d)
    (seq : S → ℕ → S) (hseq : ∀ s₀, IsAstarSeq d s₀ (seq s₀))
    (w : ℝ) (hw : (2 * (Fintype.card S : ℝ) - 1) * cycleOffsetRatio d < w) :
    ∃ K : ℝ, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      astarCost d (seq s₀) T ≤ ENNReal.ofReal (w * offlineOpt d s₀ T + K) := by sorry

end MetricalTaskSystem.Deterministic

