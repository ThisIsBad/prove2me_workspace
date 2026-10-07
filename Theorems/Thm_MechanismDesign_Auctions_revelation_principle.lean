import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.1 (Revelation Principle), p.34. A general mechanism is given by message sets
`S i`, an outcome function assigning to every message profile `s` the probabilities `alloc i s`
with which buyer `i` gets the good (a point of `Δ`) and the expected transfers `pay i s`; `σ` is a
Bayesian Nash equilibrium of the induced game of incomplete information. Then the direct
mechanism `θ ↦ (alloc (σ θ), pay (σ θ))` has truth-telling as a Bayesian Nash equilibrium
(it is incentive-compatible) and yields, at every type vector, the same allocation probabilities
and the same expected transfers as `σ` in the original mechanism. -/
theorem revelation_principle {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Environment ι)
    {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (alloc : ι → ((j : ι) → S j) → ℝ) (pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1)
    (h_alloc_meas : ∀ i, Measurable (alloc i)) (h_pay_meas : ∀ i, Measurable (pay i))
    (σ : (i : ι) → ℝ → S i) (hσ_meas : ∀ i, Measurable (σ i))
    (h_pay_int : ∀ i, Integrable (fun θ => pay i (fun j => σ j (θ j))) E.prior)
    (h_dev_int : ∀ i, ∀ s : S i,
      Integrable (fun θ => pay i (Function.update (fun j => σ j (θ j)) i s)) E.prior)
    (h_BNE : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ s : S i,
      x * ∫ θ, alloc i (Function.update (fun j => σ j (θ j)) i s) ∂E.prior
          - ∫ θ, pay i (Function.update (fun j => σ j (θ j)) i s) ∂E.prior
        ≤ x * ∫ θ, alloc i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior
          - ∫ θ, pay i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior) :
    ∃ m : DirectMechanism E, m.WellDefined ∧ m.IsIC ∧
      ∀ θ ∈ E.typeSpace, ∀ i,
        m.q i θ = alloc i (fun j => σ j (θ j)) ∧ m.t i θ = pay i (fun j => σ j (θ j)) := by sorry

end MechanismDesign.Auctions

