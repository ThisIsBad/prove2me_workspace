import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_Shared_itinerary
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.IntervalMaps

/-- Teschl, Theorem 11.5, p. 301: for `µ > 2` the dynamical systems `(Λ, T_µ)` and `(Σ₂, σ)` are
topologically equivalent (11.10) via the itinerary map `ϕ` (11.23). Spelled out: `T_µ` maps `Λ`
into itself; `ϕ` is a bijection from `Λ` onto `Σ₂`; the diagram commutes, `σ ∘ ϕ = ϕ ∘ T_µ` on
`Λ`; `ϕ` is continuous on `Λ` (subspace metric `|x − y|`) into `Σ₂` with the metric (11.24); and
its inverse is continuous, i.e. for every `x ∈ Λ` and `ε > 0` there is `δ > 0` with
`|x − y| < ε` whenever `y ∈ Λ` and `d(ϕ(y), ϕ(x)) < δ`. -/
theorem tent_topEquiv_shift (μ : ℝ) (hμ : 2 < μ) :
    Set.MapsTo (TeschlODE.Shared.tentMap μ) (TeschlODE.Shared.tentRepellor μ) (TeschlODE.Shared.tentRepellor μ) ∧
      Set.BijOn (TeschlODE.Shared.itinerary μ) (TeschlODE.Shared.tentRepellor μ) Set.univ ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.shift (TeschlODE.Shared.itinerary μ x) = TeschlODE.Shared.itinerary μ (TeschlODE.Shared.tentMap μ x)) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, |y - x| < δ → TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < ε) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < δ → |y - x| < ε) := by sorry

end TeschlODE.IntervalMaps

