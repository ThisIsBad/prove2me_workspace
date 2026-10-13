import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Proposition 7.34 (Bertsekas & Shreve, pp. 154–155). Let `X` be metrizable, `Y` separable
metrizable, `D ⊆ X × Y` open, `f : D → R*` upper semicontinuous, and
`f*(x) = inf_{y ∈ D_x} f(x, y)` on `proj_X(D)` (Eq. (67) of Chapter 7). Then `proj_X(D)` is open,
`f*` is upper semicontinuous, and for every `ε > 0` there is a Borel-measurable
`φ_ε : proj_X(D) → Y` with `Gr(φ_ε) ⊆ D` and, for all `x ∈ proj_X(D)`,
`f(x, φ_ε(x)) ≤ f*(x) + ε` if `f*(x) > −∞` and `f(x, φ_ε(x)) ≤ −1/ε` if `f*(x) = −∞`
(Eq. (68)). `f` is given on all of `X × Y`; only its values on `D` matter. -/
theorem prop7_34_usc_epsilon_selector {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (D : Set (X × Y)) (hD : IsOpen D) (f : X × Y → EReal) (hf : UpperSemicontinuousOn f D) :
    IsOpen (Prod.fst '' D) ∧
    UpperSemicontinuousOn (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) (Prod.fst '' D) ∧
    ∀ ε : ℝ, 0 < ε → ∃ φ : (Prod.fst '' D) → Y, Measurable φ ∧
      ∀ x : (Prod.fst '' D), ((x : X), φ x) ∈ D ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) ≠ ⊥ →
          f ((x : X), φ x) ≤ (⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) + (ε : EReal)) ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) = ⊥ →
          f ((x : X), φ x) ≤ ((-1 / ε : ℝ) : EReal)) := by sorry

end BertsekasShreve.SemicontSelection

