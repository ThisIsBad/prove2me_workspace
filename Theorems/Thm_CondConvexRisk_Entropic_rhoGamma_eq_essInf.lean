import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

theorem rhoGamma_eq_essInf {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    IsEssInf P
        (fun Y : {Y : Ω → ℝ // MemLp Y ⊤ P ∧ StronglyMeasurable[m] Y ∧
            X + Y ∈ acceptanceSet m P γ} => fun ω => ((Y.1 ω : ℝ) : EReal))
        (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal)) ∧
    IsEssInf P
        (fun Y : {Y : Ω → ℝ // MemLp Y ⊤ P ∧ StronglyMeasurable[m] Y ∧
            (P[fun x => Real.exp (-γ * X x) | m]) ≤ᵐ[P] fun ω => Real.exp (γ * Y ω)} =>
          fun ω => ((Y.1 ω : ℝ) : EReal))
        (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal)) := by sorry

end CondConvexRisk.Entropic
