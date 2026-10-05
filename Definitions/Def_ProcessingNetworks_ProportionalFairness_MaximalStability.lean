import Mathlib

namespace ProcessingNetworks.ProportionalFairness

/-- The stability region `Λ*` for a family of networks indexed by arrival-rate vector `lam`
(Section 5.7), restated identically in shape from mission II's `Subcriticality.StabilityRegion`
(a different sub-namespace, so no name collision, but restated here rather than cross-imported
since this chunk's own `BRIEF.md` does not list mission II as a dependency). A policy is
represented abstractly by a value of `Policy`, and `PolicyStable p lam` records that `p` is a
stable policy for arrival-rate vector `lam`. -/
def StabilityRegion {I : ℕ} {Policy : Type*} (PolicyStable : Policy → (Fin I → ℝ) → Prop) :
    Set (Fin I → ℝ) :=
  {lam | ∃ p, PolicyStable p lam}

/-- A control policy `p` is maximally stable (Section 5.7) if it is a stable policy for every
`λ` in the stability region `Λ*`, restated identically in shape from mission II's
`Subcriticality.IsMaximallyStable`. -/
def IsMaximallyStable {I : ℕ} {Policy : Type*} (PolicyStable : Policy → (Fin I → ℝ) → Prop)
    (p : Policy) : Prop :=
  ∀ lam ∈ StabilityRegion PolicyStable, PolicyStable p lam

end ProcessingNetworks.ProportionalFairness
