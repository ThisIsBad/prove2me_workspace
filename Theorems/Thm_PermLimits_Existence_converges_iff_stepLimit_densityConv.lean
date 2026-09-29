import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
import Definitions.Def_PermLimits_Shared_StepLimit
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits.Shared

namespace PermLimits.Existence

open Filter unitInterval

/-- **Eq. (49)** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2,
Sect. 5.2, p. 17). For a permutation sequence `(σ_m)` with `|σ_m| → ∞` and `Z ∈ 𝒵`,
`σ_m → Z ⟺ Z_{σ_m} →ᵗ Z`.

**Formalization Note.** The sequence is named `s` (`σ` is reserved notation once `unitInterval`
is opened). `|σ_m| → ∞` is the standing assumption the paper sets in the sentence before (49).
-/
theorem converges_iff_stepLimit_densityConv (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    ConvergesTo s Z ↔ DensityConv (fun m => stepLimit (s m).2) Z := by sorry

end PermLimits.Existence
