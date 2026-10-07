import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_RepeatedSale

namespace MechanismDesign.Dynamic

/-- **Proposition 11.12**, p.230. Let `T ≥ 1` periods, discount factor `δ ∈ [0, 1)`, and
`p* ∈ [θ̲, θ̄]` maximize `p(1 − F(p))`. The (dynamic) direct mechanism `(q*, t*)` with
`q*_τ(θ) = q̄ˢ(θ)` and `t*_τ(θ) = t̄ˢ(θ)` for all `τ = 1, …, T` — the posted price `p*` in every
period — is an optimal selling mechanism: it is incentive-compatible and individually rational,
and its expected discounted revenue is at least that of every (admissible) incentive-compatible,
individually rational dynamic direct mechanism. -/
theorem repeated_posted_price_optimal {θlo θhi : ℝ} (D : ValuationDist θlo θhi) (T : ℕ)
    (hT : 0 < T) (δ : ℝ) (hδ : δ ∈ Set.Ico (0 : ℝ) 1) (pstar : ℝ)
    (hp : pstar ∈ Set.Icc θlo θhi)
    (hmax : IsMaxOn (fun p => p * (1 - D.F p)) (Set.Icc θlo θhi) pstar) :
    (repeatedPostedPrice T θlo θhi pstar).Admissible ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIC δ ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIR δ ∧
      ∀ m : RepMechanism T θlo θhi, m.Admissible → m.IsIC δ → m.IsIR δ →
        m.revenue D δ ≤ (repeatedPostedPrice T θlo θhi pstar).revenue D δ := by sorry

end MechanismDesign.Dynamic

