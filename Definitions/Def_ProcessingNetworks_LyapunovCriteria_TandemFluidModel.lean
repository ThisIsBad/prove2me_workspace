import Mathlib

namespace ProcessingNetworks.LyapunovCriteria

/-- The fluid model of the two-station tandem queueing network (Figure 1.1, Chapter 1 — out of
series scope, restated locally per `BRIEF.md`), specialized from (6.1)-(6.6) plus the non-idling
condition (6.7): buffer 1 receives external arrivals at rate `lam1` and is served by station 1
at rate `mu1`; departures from buffer 1 feed buffer 2, served by station 2 at rate `mu2`. `Z1, Z2`
are the buffer contents, `T1, T2` the cumulative service efforts (Eqs. 8.11-8.15). -/
def TandemFluidSolution (lam1 mu1 mu2 : ℝ) (Z1 Z2 T1 T2 : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → Z1 t = Z1 0 + lam1 * t - mu1 * T1 t) ∧
  (∀ t : ℝ, 0 ≤ t → Z2 t = Z2 0 + mu1 * T1 t - mu2 * T2 t) ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ Z1 t ∧ 0 ≤ Z2 t) ∧
  (T1 0 = 0 ∧ T2 0 = 0) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ T1 t - T1 s ∧ T1 t - T1 s ≤ t - s) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → 0 ≤ T2 t - T2 s ∧ T2 t - T2 s ≤ t - s) ∧
  (∀ t : ℝ, 0 < t → 0 < Z1 t → ∀ d, HasDerivAt T1 d t → d = 1) ∧
  (∀ t : ℝ, 0 < t → 0 < Z2 t → ∀ d, HasDerivAt T2 d t → d = 1)

/-- Definition 6.3 (fluid model stability), specialized to the tandem queueing network's fluid
model: there is `γ > 0` such that every solution has `Z1(t) = Z2(t) = 0` for `t ≥ γ(Z1(0)+Z2(0))`. -/
def TandemFluidStable (lam1 mu1 mu2 : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∀ (Z1 Z2 T1 T2 : ℝ → ℝ), TandemFluidSolution lam1 mu1 mu2 Z1 Z2 T1 T2 →
    ∀ t : ℝ, γ * (Z1 0 + Z2 0) ≤ t → Z1 t = 0 ∧ Z2 t = 0

end ProcessingNetworks.LyapunovCriteria
