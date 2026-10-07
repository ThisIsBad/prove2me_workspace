import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Eq. (1.3.10): the Miyazawa (rate) conservation principle (§1.3.3, pp.23-24)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Miyazawa conservation principle**, Eq. (1.3.10) (§1.3.3, p.24). Let `{Y(t)}` be a
bounded real-valued corlol process compatible with the flow `{θ_t}`, let `N` be a point process
compatible with `{θ_t}` with non-null finite intensity `λ`, and let `{Y'(t)}` be a real-valued
process compatible with `{θ_t}` such that

`(1.3.9)  Y(1) = Y(0) + ∫_0^1 Y'(s) ds + ∫_{(0,1]} (Y(s) - Y(s-)) N(ds)`

— for instance `N` counts the discontinuity points of `{Y(t)}` and `Y'(t)` is the derivative of
`Y(t)` between them. Then

`(1.3.10)  E[Y'(0)] + λ E⁰_N[ Y(0) - Y(0-) ] = 0`:

the mean drift of the continuous part is exactly cancelled by the mean jump rate. This is the
*(rate) conservation principle*, which Chapter 3 applies repeatedly.

The boundedness of `{Y(t)}` is the hypothesis the book states; Remark 1.3.4 on p.24 records three
alternatives to it, recorded in `MODERATION_NOTES.md` rather than stated here. `hY'int` makes
explicit that `E[Y'(0)]` in (1.3.10) is a finite expectation, as the book's formula presupposes:
without it a Bochner integral of a non-integrable `Y'(0)` would silently read as `0`. -/
theorem miyazawa_conservation (S : PalmSetting Ω) (Y Yl Y' : ℝ → Ω → ℝ)
    (hYbdd : ∃ C : ℝ, ∀ (t : ℝ) (ω : Ω), |Y t ω| ≤ C)
    (hYmeas : ∀ t, Measurable (Y t)) (hYlmeas : ∀ t, Measurable (Yl t))
    (hY'meas : ∀ t, Measurable (Y' t)) (hY'int : Integrable (Y' 0) S.P)
    (hYright : ∀ (s : ℝ) (ω : Ω), ContinuousWithinAt (fun u => Y u ω) (Set.Ici s) s)
    (hYleft : IsLeftLimitProcess Y Yl)
    (hYcomp : IsCompatible S.θ Y) (hY'comp : IsCompatible S.θ Y')
    (hjump : ∀ ω, Y 1 ω = Y 0 ω + (∫ s in Set.Ioc (0 : ℝ) 1, Y' s ω ∂(volume : Measure ℝ))
        + ∫ s in Set.Ioc (0 : ℝ) 1, (Y s ω - Yl s ω) ∂(S.N.count ω)) :
    (∫ ω, Y' 0 ω ∂S.P) + S.lam * ∫ ω, (Y 0 ω - Yl 0 ω) ∂S.P0 = 0 := by sorry

end PalmQueueing.Palm

