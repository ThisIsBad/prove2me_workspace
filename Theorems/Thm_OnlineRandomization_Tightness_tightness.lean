import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model

namespace OnlineRandomization.Tightness

open MeasureTheory

/-- Manuscript p. 11, §2, tightness of Theorem 2.2 (construction pp. 12–13), for
`1 < β ≤ α` (and the trivial case `α = β = 1`): for every `C < αβ` there are a request-answer
game and a randomized algorithm `G` that is `α`-competitive against any adaptive on-line
adversary and `β`-competitive against any oblivious adversary, while against every randomized
algorithm `K` some adaptive off-line adversary forces the ratio `C` (with a positive expected
adversary cost). -/
theorem tightness (α β C : ℝ) (hαβ : (1 < β ∧ β ≤ α) ∨ (β = 1 ∧ α = 1)) (hC : C < α * β) :
    ∃ (R A Ω : Type) (_ : Fintype A) (_ : Nonempty A) (_ : MeasurableSpace Ω)
      (F : Game R A) (G : RandAlg R A Ω),
      IsCompetitiveOnline F (fun x => α * x) G ∧
      IsCompetitiveObl F (fun x => β * x) G ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (K : RandAlg R A Ω'),
        ∃ Q : OfflineAdv R A,
          0 < ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ∧
          C * ∫ ω, advCostOffline F (K.alg ω) Q ∂K.μ ≤
            ∫ ω, algCostOffline F (K.alg ω) Q ∂K.μ := by sorry

end OnlineRandomization.Tightness

