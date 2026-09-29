import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_StepLimit
open PermLimits.Shared

namespace PermLimits.Existence

open unitInterval

/-- **Lemma 3.5** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 11).
Let `τ ∈ S_k`, `π ∈ S_n`, `k ≤ n`. Then `|t(τ, π) − t(τ, Z_π)| ≤ (1/n) · C(k, 2)` (Eq. (27)).

**Formalization Note.** The paper's permutation is called `σ`; here `π` (`σ` is reserved notation
once `unitInterval` is opened). `k ≥ 1` is the paper's standing convention that `τ ∈ S_k` for a
positive integer `k` (Definition 1.1); with `k ≤ n` it gives `n ≥ 1`, so `1/n` is a genuine
quotient. -/
theorem density_stepLimit_close {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (hk : 0 < k) (hkn : k ≤ n) :
    |permDensity τ π - limitDensity τ (stepLimit π)| ≤ (1 / (n : ℝ)) * (Nat.choose k 2 : ℝ) := by sorry

end PermLimits.Existence
