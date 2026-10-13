import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Proof of Theorem 1, (27)–(28)** (Satterthwaite, p. 27). In the proof's case of a
strategy-proof, strong alternative-excluding strict voting procedure `f` with a proper range
`T = T_p` of at least three alternatives, `f` factors through the restriction of ballots to `T`:
there is a
strict voting procedure `g` for the alternative set `T` (a subtype) with
`g(θ_T(B_1), …, θ_T(B_n)) = f(B)` for every strict ballot set `B`, and `g` is strategy-proof. -/
theorem restriction_factor {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι)
    (f : (ι → A → A → Prop) → A) (hsp : IncentiveCompatible f)
    (hstrong : StrongAltExcluding f)
    (hp : 3 ≤ (range f).ncard)
    (hproper : (range f).ncard < Fintype.card A) :
    ∃ g : (ι → range f → range f → Prop) → range f,
      (∀ P : ι → A → A → Prop, IsPrefProfile P →
        ((g (fun i (x y : range f) => P i x y) : A) = f P)) ∧
      IncentiveCompatible g := by sorry

end StrategyProofArrow.Dictatorship

