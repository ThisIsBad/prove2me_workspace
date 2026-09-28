import Mathlib
import Definitions.Def_GPSAnalysis_Core_Mesh

open Matrix

namespace GPSAnalysis.Core

/-- Lemma 3.2 (Audet–Dennis 2003, p. 895). Let `N` be a norm on `ℝⁿ` for which every nonzero
integer vector has norm at least `1`, and let `c` bound the operator norm of `G⁻¹` induced by `N`
(`N(G⁻¹ v) ≤ c N(v)` for all `v`; the least such `c` is `‖G⁻¹‖`). Then any two distinct points
of the mesh `M_k` (2.4) built from `D = G Z̄` are at `N`-distance at least `Δ_k / c`. -/
theorem mesh_separation {n p : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G.det)
    (Zbar : Matrix (Fin n) (Fin p) ℤ) (xk : Fin n → ℝ) (Δk : ℝ) (hΔk : 0 < Δk)
    (N : AddGroupNorm (Fin n → ℝ)) (hN_smul : ∀ (a : ℝ) (v : Fin n → ℝ), N (a • v) = |a| * N v)
    (hN_int : ∀ z : Fin n → ℤ, z ≠ 0 → 1 ≤ N (fun i => (z i : ℝ)))
    (c : ℝ) (hc : ∀ v : Fin n → ℝ, N (G⁻¹ *ᵥ v) ≤ c * N v) :
    ∀ u ∈ mesh (dirMatrix G Zbar) xk Δk, ∀ v ∈ mesh (dirMatrix G Zbar) xk Δk,
      u ≠ v → Δk / c ≤ N (u - v) := by sorry

end GPSAnalysis.Core
