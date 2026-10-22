import Definitions.Def_Kall1976_RecourseDifferentiability

open MeasureTheory


namespace Kall1976

/-- Kall (1976), III.12, printed48 / PDF54, with III.10/11 alternatives.
The derivative is within the source feasible domain, including its boundary.
A continuous field of linear functionals represents the continuous gradient
in finite coordinates. No complete recourse or interior-only substitution.
The first conjuncts make the reused real expectation faithful on that domain;
they are included consequences of the cited integrability hypotheses. -/
theorem expected_recourse_contDiffOn {m n p : ℕ}
    (μ : Measure (RecourseData m n p)) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin p) ℝ)
    (hmom : recourseMomentAlternative μ)
    (hbelow : ∀ x ∈ recourseDomain μ W, ⊥ < extendedExpectedRecourse μ W x)
    (hdensity : μ ≪ volume) :
    (∀ x ∈ recourseDomain μ W,
      (∀ᵐ d ∂μ, ∃ v : ℝ,
        KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x = (v : EReal)) ∧
      Integrable (fun d =>
        (KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toReal) μ) ∧
    ∃ g : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ),
      ContinuousOn g (recourseDomain μ W) ∧
      ∀ x ∈ recourseDomain μ W,
        HasFDerivWithinAt
          (KallMayer.Recourse.ExpectedRecourse μ W
            (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2))
          (g x) (recourseDomain μ W) x := by sorry

end Kall1976

