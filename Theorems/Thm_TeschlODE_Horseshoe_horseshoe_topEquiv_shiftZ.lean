import Mathlib
import Definitions.Def_TeschlODE_Horseshoe_IsHorseshoeMap
import Definitions.Def_TeschlODE_Horseshoe_horseshoeSet
import Definitions.Def_TeschlODE_Horseshoe_horseshoeItinerary
import Definitions.Def_TeschlODE_Horseshoe_shiftZ
import Definitions.Def_TeschlODE_Horseshoe_symDistZ
import Definitions.Def_TeschlODE_Horseshoe_IsCantorSet
import Definitions.Def_TeschlODE_Shared_IsChaotic

namespace TeschlODE.Horseshoe

/-- Teschl, Theorem 13.1, p. 333: the Smale horseshoe map has an invariant Cantor set `Λ` on which
the dynamics is equivalent to the double sided shift on two symbols; in particular it is
chaotic.

Here `F` is any map agreeing with (13.2) on `J₀` and with (13.3) on `J₁` (its values elsewhere
are arbitrary, as in the book), `Λ = Λ(T_{1/λ}) × Λ(T_µ)` is the set (13.8), and `ϕ` is the
itinerary map (13.9). The conclusion: `Λ` is a Cantor set; `F(Λ) = Λ`; `ϕ` is a bijection from
`Λ` onto `Σ₂ = {0, 1}^ℤ`; `σ ∘ ϕ = ϕ ∘ F` on `Λ` (σ the two-sided shift); `ϕ` and `ϕ⁻¹` are
continuous (ε–δ, `Λ ⊆ ℝ²` with its usual topology and `Σ₂` with the metric (11.35)); and the
restricted system `(Λ, F|_Λ)` is chaotic in the sense of p. 296.

Correction to the page: the book fixes `λ ∈ (0, 1/2]`, `µ ∈ [2, ∞)`. At `µ = 2` the strips `J₀`,
`J₁` meet on `y = 1/2`, where (13.2) and (13.3) disagree, and `Λ(T₂) = [0, 1]` is not a Cantor
set; at `λ = 1/2` the images `K₀`, `K₁` meet and `Λ(T₂) = [0, 1]` again. The theorem is stated for
`λ ∈ (0, 1/2)` and `µ > 2`. -/
theorem horseshoe_topEquiv_shiftZ (lam μ : ℝ) (hlam₀ : 0 < lam) (hlam : lam < 1 / 2)
    (hμ : 2 < μ) (F : ℝ × ℝ → ℝ × ℝ) (hF : IsHorseshoeMap lam μ F) :
    IsCantorSet (horseshoeSet lam μ) ∧
      F '' horseshoeSet lam μ = horseshoeSet lam μ ∧
      Set.BijOn (horseshoeItinerary lam μ F) (horseshoeSet lam μ) Set.univ ∧
      (∀ p ∈ horseshoeSet lam μ,
        shiftZ (horseshoeItinerary lam μ F p) = horseshoeItinerary lam μ F (F p)) ∧
      (∀ p ∈ horseshoeSet lam μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ q ∈ horseshoeSet lam μ, dist q p < δ →
          symDistZ 2 (horseshoeItinerary lam μ F q) (horseshoeItinerary lam μ F p) < ε) ∧
      (∀ p ∈ horseshoeSet lam μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ q ∈ horseshoeSet lam μ,
          symDistZ 2 (horseshoeItinerary lam μ F q) (horseshoeItinerary lam μ F p) < δ →
            dist q p < ε) ∧
      ∃ h : Set.MapsTo F (horseshoeSet lam μ) (horseshoeSet lam μ),
        TeschlODE.Shared.IsChaotic (h.restrict F (horseshoeSet lam μ) (horseshoeSet lam μ)) := by sorry

end TeschlODE.Horseshoe

