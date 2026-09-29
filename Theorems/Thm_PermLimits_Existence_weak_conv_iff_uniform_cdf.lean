import Mathlib
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits.Shared

namespace PermLimits.Existence

open MeasureTheory Filter unitInterval

/-- **Lemma 2.1** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 7).
Let `(μ_n)` and `μ` be probability measures on `[0,1]²`, with joint distribution functions
`F_n` and `F`, and assume that for every `n` both marginals of `μ_n` are uniform on `[0, 1]`.
Then `μ_n ⇒ μ` (convergence in distribution `(X_n, Y_n) →ᵈ (X, Y)`) if and only if
`‖F_n − F‖_∞ = sup_{x,y ∈ [0,1]} |F_n(x, y) − F(x, y)| → 0`.

**Formalization Note.** Weak convergence is the paper's (9) with continuous test functions on the
compact square (`WeakConvMeasures`). `‖F_n − F‖_∞ → 0` is `TendstoUniformly` of the joint
distribution functions on `[0,1]²`. No marginal assumption is made on `μ`, as in the paper. -/
theorem weak_conv_iff_uniform_cdf (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) [IsProbabilityMeasure μ]
    (hX : ∀ n, (μs n).map Prod.fst = volume) (hY : ∀ n, (μs n).map Prod.snd = volume) :
    WeakConvMeasures μs μ ↔
      TendstoUniformly (fun n (p : I × I) => jointCDF (μs n) p.1 p.2)
        (fun p : I × I => jointCDF μ p.1 p.2) atTop := by sorry

end PermLimits.Existence
