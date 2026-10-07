import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Proposition 2.5**, p.17 (the goal). Suppose `p* ∈ argmax_{p ∈ [θ̲, θ̄]} p (1 − F(p))`. The
posted-price mechanism — `q(θ) = 1`, `t(θ) = p*` if `θ > p*`, and `q(θ) = 0`, `t(θ) = 0` if
`θ < p*` — maximizes the seller's expected revenue among all incentive-compatible, individually
rational direct mechanisms.

Stated as: (1) the version with `q(p*) = 1`, `t(p*) = p*` is incentive-compatible and
(2) individually rational; (3) every incentive-compatible, individually rational direct mechanism
that agrees with the displayed `q` and `t` at every `θ ≠ p*` has expected revenue at least that of
every incentive-compatible, individually rational direct mechanism (whose `q` may take any value
in `[0, 1]`, i.e. randomized mechanisms are included). -/
theorem posted_price_optimal {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) (pstar : ℝ)
    (hp : pstar ∈ Set.Icc θlo θhi)
    (hmax : IsMaxOn (fun p => p * (1 - D.F p)) (Set.Icc θlo θhi) pstar) :
    (postedPrice θlo θhi pstar).IsIC ∧ (postedPrice θlo θhi pstar).IsIR ∧
      ∀ m : DirectMechanism θlo θhi,
        (∀ θ ∈ Set.Icc θlo θhi, θ ≠ pstar →
          m.q θ = (if pstar < θ then 1 else 0) ∧ m.t θ = (if pstar < θ then pstar else 0)) →
        m.IsIC → m.IsIR →
        ∀ m' : DirectMechanism θlo θhi, m'.IsIC → m'.IsIR →
          expectedRevenue D m' ≤ expectedRevenue D m := by sorry

end MechanismDesign.Screening

