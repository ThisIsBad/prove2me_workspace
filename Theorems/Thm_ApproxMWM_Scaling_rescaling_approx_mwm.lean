import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Matching

namespace ApproxMWM.Scaling

/-- Section 2, display on pp. 1:8–1:9 (Duan–Pettie, J. ACM 61(1) 2014): rounding the weights.
Let `G` have `n = |V|` vertices and nonnegative edge weights `w` with maximum
`w_max = max_e w(e) > 0`, and let `0 < ε < 1`. Put `γ_r = ε · w_max / n` and
`w̃(e) = ⌊w(e) / γ_r⌋`. If `M` is a `(1 - ε/2)`-MWM with respect to `w̃`, then
`w(M) > (1 - ε) · w(M')` for every matching `M'` of `G`; in particular `M` is a `(1 - ε)`-MWM
with respect to `w`. -/
theorem rescaling_approx_mwm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε wmax : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hw_nonneg : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hwmax_ge : ∀ e ∈ G.edgeSet, w e ≤ wmax)
    (hwmax_att : ∃ e ∈ G.edgeSet, w e = wmax)
    (hwmax_pos : 0 < wmax)
    (M : Finset (Sym2 V))
    (hM : IsApproxMWM G (fun e => ((⌊w e / (ε * wmax / (Fintype.card V : ℝ))⌋ : ℤ) : ℝ))
      (1 - ε / 2) M) :
    IsMatching G M ∧ ∀ M' : Finset (Sym2 V), IsMatching G M' → (1 - ε) * weight w M' < weight w M := by sorry

end ApproxMWM.Scaling
