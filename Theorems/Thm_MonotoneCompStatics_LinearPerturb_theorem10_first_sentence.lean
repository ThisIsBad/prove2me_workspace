import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.LinearPerturb

/-- Milgrom and Shannon (1994), p. 166, Theorem 10, first sentence: for `f : ℝⁿ × ℝ → ℝ`,
`f(x, t) + p · x` is quasisupermodular in `x` and has the single crossing property in `(x; t)`
for all `p ∈ ℝⁿ` if and only if `f` is supermodular (jointly in `(x, t)`, on the product lattice
`ℝⁿ × ℝ`). -/
theorem theorem10_first_sentence {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) :
    (∀ p : Fin n → ℝ, (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
        MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) ↔
      Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ := by sorry

end MonotoneCompStatics.LinearPerturb

