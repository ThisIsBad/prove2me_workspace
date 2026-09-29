import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Matching

namespace ApproxMWM.Scaling

/-- Lemma 2.3 (Duan–Pettie, J. ACM 61(1) 2014, pp. 1:11–1:12). Let `M` be a matching of `G`, `Ω` a
laminar set of full blossoms with respect to `M` (edge sets `EB`), and `y`, `z` dual values
satisfying Property 2.2(1,2): nonnegativity (`z(B) ≥ 0` on odd sets, `y ≥ 0`, `y(u) > 0` only at
matched `u`) and active blossoms (`z(B) > 0` only for `B ∈ Ω`, every root blossom has
`z(B) > 0`); approximate domination `yz(e) ≥ (1 - ε₀) w(e)` on every edge; approximate tightness
`yz(e) ≤ (1 + ε₁) w(e)` on `M ∪ ⋃_{B ∈ Ω} E_B`; and zero `y` on free vertices. Then `M` is a
`(1 + ε₁)⁻¹ (1 - ε₀)`-MWM. The page does not bound `ε₀, ε₁`; the only range used is
`1 + ε₁ > 0`. -/
theorem approx_slackness_approx_mwm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (M : Finset (Sym2 V)) (Ω : Finset (Finset V))
    (EB : Finset V → Finset (Sym2 V)) (y : V → ℝ) (z : Finset V → ℝ) (ε₀ ε₁ : ℝ)
    (hε₁ : -1 < ε₁)
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω EB)
    (hz_nonneg : ∀ B : Finset V, Odd B.card → 0 ≤ z B)
    (hy_nonneg : ∀ u : V, 0 ≤ y u)
    (hy_matched : ∀ u : V, 0 < y u → IsMatched M u)
    (hz_active : ∀ B : Finset V, Odd B.card → 0 < z B → B ∈ Ω)
    (hz_root : ∀ B : Finset V, IsRoot Ω B → 0 < z B)
    (hdom : ∀ e ∈ G.edgeSet, (1 - ε₀) * w e ≤ yz y z e)
    (htight : ∀ e ∈ G.edgeSet, (e ∈ M ∨ ∃ B ∈ Ω, e ∈ EB B) → yz y z e ≤ (1 + ε₁) * w e)
    (hfree : ∀ u : V, IsFree M u → y u = 0) :
    IsApproxMWM G w ((1 + ε₁)⁻¹ * (1 - ε₀)) M := by sorry

end ApproxMWM.Scaling
