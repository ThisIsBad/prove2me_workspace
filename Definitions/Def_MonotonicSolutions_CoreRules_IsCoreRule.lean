import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MonotonicSolutions_CoreRules_Game

namespace MonotonicSolutions.CoreRules

/-- A core allocation rule (Young 1985, p. 68): whenever the core
`{x | ∑_{i ∈ N} x i = v N ∧ ∀ S, v S ≤ ∑_{i ∈ S} x i}` of the game `v` is nonempty,
`φ v` lies in it. Games with an empty core are unconstrained. -/
def IsCoreRule {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v : Game n, (Supermodularity.Cooperative.Core Finset.univ v.1).Nonempty →
    φ v ∈ Supermodularity.Cooperative.Core Finset.univ v.1

end MonotonicSolutions.CoreRules
