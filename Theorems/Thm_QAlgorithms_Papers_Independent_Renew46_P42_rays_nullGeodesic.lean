import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.6, (50)–(51), Gordon [2]: rays of the laboratory Hamiltonian are null
geodesics in laboratory time, with acceleration parallel to their tangent.
This avoids any global minimum claim for Lorentzian length. -/
theorem rays_nullGeodesic (c : ℝ) (P : OpticalPatch c)
    (I : Set ℝ) (q : ℝ → V4) (k : ℝ → V3)
    (hc : 0 < c) (hI : IsOpen I)
    (hq : ContDiffOn ℝ 2 q I) (hkreg : ContDiffOn ℝ 1 k I)
    (himage : ∀ t ∈ I, q t ∈ P.domain)
    (hkn : ∀ t ∈ I, k t ≠ 0)
    (ht : ∀ t ∈ I, q t 0 = c * t)
    (hposition : ∀ t ∈ I,
      spatial (deriv q t) = rayVelocity c (P.index (q t)) (P.flow (q t)) (k t))
    (hmomentum : ∀ t ∈ I,
      deriv k t = -spatial (gradient (fun x =>
        rayHamiltonian c (P.index x) (P.flow x) (k t)) (q t))) :
    (∀ t ∈ I, quadratic (patchDown P (q t)) (deriv q t) = 0 ∧
      ∃ a : ℝ, covAcceleration (patchDown P) (patchUp P) q t = a • deriv q t) ∧
    (∀ x ∈ P.domain, ∀ v : V4,
      quadratic (patchDown P x) (apply4 (lorentzBoost c (P.flow x)) v) =
        (v 0) ^ 2 / (P.index x) ^ 2 - ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2)) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42

