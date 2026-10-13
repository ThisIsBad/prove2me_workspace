import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 4** (Satterthwaite, p. 22). Three alternatives, `n ≥ 1`. If every strategy-proof
strict voting procedure for the `n` individuals `ι` is fully dictatorial or strong
alternative-excluding, then every strategy-proof strict voting procedure for the `n + 1`
individuals `Option ι` with `1 ≤ p ≤ 3` is fully dictatorial or strong alternative-excluding. -/
theorem lemma_4 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hm : Fintype.card A = 3)
    (hind : ∀ g : (ι → A → A → Prop) → A, IncentiveCompatible g →
      FullyDictatorial g ∨ StrongAltExcluding g)
    (f : (Option ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f) :
    FullyDictatorial f ∨ StrongAltExcluding f := by sorry

end StrategyProofArrow.Dictatorship

