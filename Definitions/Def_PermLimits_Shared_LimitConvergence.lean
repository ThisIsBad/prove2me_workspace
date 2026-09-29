import Mathlib
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_RectDist

/-!
# Three notions of convergence of limit permutations

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2: weak convergence, Eq. (9) (p. 7), and Definition 5.2 (p. 16).

A definition bundle: weak convergence of measures on `[0,1]²`, and the convergences `Z_n ⇒ Z`,
`Z_n →□ Z`, `Z_n →ᵗ Z` of Definition 5.2.
-/

namespace PermLimits.Shared

open MeasureTheory Filter Topology unitInterval

/-- **Weak convergence** `μ_n ⇒ μ` of measures on `[0,1]²` (Hoppen et al., arXiv:1103.5844v2,
Sect. 2.2, Eq. (9), p. 7): `∫ f dμ_n → ∫ f dμ` for every bounded continuous `f : [0,1]² → ℝ`.
For random points this is convergence in distribution `(X_n, Y_n) →ᵈ (X, Y)`.

**Formalization Note.** `[0,1]²` is compact, so every continuous `f` is bounded; the test
functions are `C(I × I, ℝ)`. The predicate is applied to probability measures. -/
def WeakConvMeasures (μs : ℕ → Measure (I × I)) (μ : Measure (I × I)) : Prop :=
  ∀ f : C(I × I, ℝ), Tendsto (fun n => ∫ p, f p ∂(μs n)) atTop (𝓝 (∫ p, f p ∂μ))

/-- **`Z_n ⇒ Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 5.2 (1), p. 16): the random
points associated with `Z_n` converge in distribution to the one associated with `Z`, i.e.
`μ_{Z_n} ⇒ μ_Z`. -/
def WeakConv (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ) : Prop :=
  WeakConvMeasures (fun n => limitMeasure (Zs n)) (limitMeasure Z)

/-- **`Z_n →□ Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 5.2 (2), p. 16):
`lim_n d□(Z_n, Z) = 0`. -/
def RectConv (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ) : Prop :=
  Tendsto (fun n => rectDist (Zs n) Z) atTop (𝓝 0)

/-- **`Z_n →ᵗ Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 5.2 (3), p. 16):
`lim_n t(τ, Z_n) = t(τ, Z)` for every permutation `τ`.

**Formalization Note.** `τ` ranges over permutations of every length `k`; for `k = 0` the clause
is `1 → 1`. -/
def DensityConv (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ) : Prop :=
  ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)),
    Tendsto (fun n => limitDensity τ (Zs n)) atTop (𝓝 (limitDensity τ Z))

end PermLimits.Shared
