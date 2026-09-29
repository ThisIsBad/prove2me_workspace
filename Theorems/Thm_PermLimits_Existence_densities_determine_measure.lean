import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitMeasure
open PermLimits.Shared

namespace PermLimits.Existence

open unitInterval

/-- **Lemma 5.1** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 15).
Let `Z, Ẑ ∈ 𝒵`, with associated random points `(X, Y)` and `(X̂, Ŷ)` (Definition 2.3). If
`t(τ, Z) = t(τ, Ẑ)` for every permutation `τ`, then `(X, Y) ∼ (X̂, Ŷ)`.

**Formalization Note.** The paper's `Ẑ` is written `Z'`. `(X, Y) ∼ (X̂, Ŷ)` (same distribution, Sect. 2.1, p. 6) is equality of
the laws `limitMeasure Z = limitMeasure Ẑ`. `τ` ranges over permutations of every length. -/
theorem densities_determine_measure (Z Z' : I → I → ℝ) (hZ : IsLimitPerm Z) (hZ' : IsLimitPerm Z')
    (h : ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)), limitDensity τ Z = limitDensity τ Z') :
    limitMeasure Z = limitMeasure Z' := by sorry

end PermLimits.Existence
