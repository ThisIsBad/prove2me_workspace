import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 2, p. 34: at Step 2 the alternating sequence `Z₀, Z₁, …, Z₂ₖ` exists (it stops),
it is uniquely specified, its elements are distinct, and `Z₀` is the only non-covered primed
zero. -/
theorem step2_sequence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (z₀ : Fin n × Fin n) (hs : Reachable A s) (hph : s.phase = Phase.step2 z₀) :
    (∃ zs, IsStep2Seq s z₀ zs) ∧
    (∀ zs zs', IsStep2Seq s z₀ zs → IsStep2Seq s z₀ zs' → zs = zs') ∧
    (∀ zs, IsStep2Seq s z₀ zs → zs.Nodup) ∧
    (z₀ ∈ s.primed ∧ NonCovered s z₀ ∧ ∀ p ∈ s.primed, NonCovered s p → p = z₀) := by sorry

end MunkresAlg.Assignment

