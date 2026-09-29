import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitMeasure

/-!
# Convergence of a permutation sequence to a limit permutation

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 4, Definition 1.5, Eq. (5).
-/

namespace PermLimits.Shared

open Filter Topology unitInterval

/-- **`σ_m → Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 1.5, Eq. (5), p. 4). For a
permutation sequence `(σ_m)` with `|σ_m| → ∞` and `Z ∈ 𝒵`, `σ_m → Z` means
`lim_m t(τ, σ_m) = t(τ, Z)` for every permutation `τ`.

**Formalization Note.** The standing hypothesis `|σ_m| → ∞` of Definition 1.5 is made the first
conjunct, so `ConvergesTo s Z` asserts it. The sequence is named `s` (`σ` is reserved
notation once `unitInterval` is opened). The hypothesis `Z ∈ 𝒵` is not part of this predicate;
every statement using it assumes `IsLimitPerm Z` separately. `τ` ranges over permutations of every
length `k` (a length-`0` pattern gives the trivially true clause `1 → 1`). -/
def ConvergesTo (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) (Z : I → I → ℝ) : Prop :=
  Tendsto (fun m => (s m).1) atTop atTop ∧
  ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)),
    Tendsto (fun m => permDensity τ (s m).2) atTop (𝓝 (limitDensity τ Z))

end PermLimits.Shared
