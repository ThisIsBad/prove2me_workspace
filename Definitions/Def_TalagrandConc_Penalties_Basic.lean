import Mathlib

open MeasureTheory

namespace TalagrandConc.Penalties

open Classical in
/-- The penalized distance (2.4.1) from `x ∈ Ω^N` to `A ⊆ Ω^N` for a penalty `h : Ω → Ω → ℝ`:
`f_h(A,x) = inf { ∑_{i} h(x_i, y_i) 1_{x_i ≠ y_i} ; y ∈ A }`, computed in `ℝ≥0∞`
(so `f_h(∅, x) = ⊤`). Under (2.4.2) `h(x,x) = 0` this is (2.4.3). -/
noncomputable def fh {Ω : Type*} {N : ℕ} (h : Ω → Ω → ℝ) (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ENNReal :=
  ⨅ y ∈ A, ∑ i, ENNReal.ofReal (if x i = y i then 0 else h (x i) (y i))

/-- The symmetrized penalty `v(ω, ω') = max(h(ω, ω'), h(ω', ω))` of Theorem 2.4.1. -/
def vmax {Ω : Type*} (h : Ω → Ω → ℝ) (ω ω' : Ω) : ℝ :=
  max (h ω ω') (h ω' ω)

/-- The transform (2.4.5) of Proposition 2.4.2: `ĝ(x) = inf_{y ∈ Ω} (g(y) + t h(x, y))`.
(For `g ≥ 0`, `h ≥ 0`, `t > 0` the family is bounded below by `0`, so the real infimum is the
true infimum whenever `Ω` is nonempty.) -/
noncomputable def ghat {Ω : Type*} (t : ℝ) (h : Ω → Ω → ℝ) (g : Ω → ℝ) (x : Ω) : ℝ :=
  ⨅ y : Ω, (g y + t * h x y)

/-- The functional (2.5.1): `h(ω, B) = inf { h(ω, ω') ; ω' ∈ B }` for `B ⊆ Ω`, computed in
`ℝ≥0∞` (so `h(ω, ∅) = ⊤`). -/
noncomputable def hSet {Ω : Type*} (h : Ω → Ω → ℝ) (ω : Ω) (B : Set Ω) : ENNReal :=
  ⨅ ω' ∈ B, ENNReal.ofReal (h ω ω')

/-- The transform (2.5.7) of Proposition 2.5.2: with `B_s = {g ≤ s}`,
`ĝ(x) = inf_{s > 0} (s + t h(x, B_s))`, computed in `ℝ≥0∞`. -/
noncomputable def ghatLevel {Ω : Type*} (t : ℝ) (h : Ω → Ω → ℝ) (g : Ω → ℝ) (x : Ω) : ENNReal :=
  ⨅ s : ℝ, ⨅ (_ : 0 < s), ENNReal.ofReal s + ENNReal.ofReal t * hSet h x {y | g y ≤ s}

/-- The upper integral `∫* F dμ = inf { ∫ G dμ ; G measurable, F ≤ G }` of a possibly
non-measurable `F : Ω → ℝ≥0∞` (pp. 81–82). It equals `∫⁻ F dμ` when `F` is measurable. -/
noncomputable def upperLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ENNReal) : ENNReal :=
  ⨅ (G : Ω → ENNReal) (_ : Measurable G) (_ : F ≤ G), ∫⁻ x, G x ∂μ

end TalagrandConc.Penalties
