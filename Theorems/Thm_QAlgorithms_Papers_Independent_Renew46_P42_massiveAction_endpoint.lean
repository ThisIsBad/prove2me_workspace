import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.5–6, (39)–(49): zero massless Legendre transform and the massive
proper-length action on an actual local geodesic endpoint congruence.
The mass m is an artificial regularization, not a photon mass. -/
theorem massiveAction_endpoint (c m : ℝ) (P : OpticalPatch c)
    (q : ℝ → V4 → V4) (z zBase : V4) (J : Set ℝ) (E : Set V4)
    (hc : 0 < c) (hm : 0 < m) (hz : z ∈ E)
    (hE : IsOpen E) (hEP : E ⊆ P.domain)
    (hJ : IsOpen J) (h01 : Icc (0 : ℝ) 1 ⊆ J)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E))
    (hend : ∀ y ∈ E, q 0 y = zBase ∧ q 1 y = y)
    (himage : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1, q s y ∈ P.domain)
    (htime : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      0 < deriv (fun t => q t y) s 0)
    (htimelike : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      0 < quadratic (patchDown P (q s y)) (deriv (fun t => q t y) s))
    (hgeo : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      covAcceleration (patchDown P) (patchUp P) (fun t => q t y) s = 0) :
    (∀ k : V3, k ≠ 0 →
      dot3 k (rayVelocity c (P.index z) (P.flow z) k) -
        rayHamiltonian c (P.index z) (P.flow z) k = 0) ∧
    (∀ v : V3, 0 < quadratic (patchDown P z) ![c, v 0, v 1, v 2] →
      massiveLagrangian c (P.index z) m (P.flow z) v =
        -m * c * Real.sqrt (quadratic (patchDown P z) ![c, v 0, v 1, v 2])) ∧
    DifferentiableAt ℝ (endpointAction P m q) z ∧
    (∀ i : Fin 4, -cartesianPartial (endpointAction P m q) z i =
      massiveCovector c m (patchDown P z) (deriv (fun s => q s z) 1) i) ∧
    quadratic (patchUp P z) (gradient (endpointAction P m q) z) = m ^ 2 * c ^ 2 := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42

