import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 3** (Satterthwaite, pp. 16–17). Let the committee have `n + 1` individuals, encoded as
`Option ι` with `none` the individual `n + 1`, three alternatives, `n ≥ 1` and `1 ≤ p ≤ 3`. No
individual `i ∈ I_n` (individual `n + 1` excluded) can manipulate `f` at any strict ballot set if
and only if every section `sectionAt f b` (voter `n + 1` casting the strict ballot `b`) is a
strategy-proof strict voting procedure for the `n` remaining individuals. -/
theorem lemma_3 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : Fintype.card A = 3)
    (f : (Option ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard) :
    (∀ P : Option ι → A → A → Prop, IsPrefProfile P →
        ∀ (i : ι) (r' : A → A → Prop), IsStrictTotalOrder A r' →
          ¬ P (some i) (f (Function.update P (some i) r')) (f P)) ↔
      ∀ b : A → A → Prop, IsStrictTotalOrder A b → IncentiveCompatible (sectionAt f b) := by sorry

end StrategyProofArrow.Dictatorship

