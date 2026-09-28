import Mathlib

namespace LogRegretOCO.ONS

open scoped MatrixOrder Matrix

theorem aux_logdet_le_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    Real.log M.det ≤ M.trace - n := by
  rw [hM.1.det_eq_prod_eigenvalues, hM.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [Real.log_prod (fun i _ => (hM.eigenvalues_pos i).ne')]
  have : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hM.eigenvalues_pos i)

theorem aux_logdet_main {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : (A - B).PosSemidef) (hB : B.PosDef) :
    ∑ i, ∑ j, A⁻¹ i j * (A - B) i j ≤ Real.log (A.det / B.det) := by
  have hA : A.PosDef := by
    have h := hB.add_posSemidef hAB
    rwa [add_sub_cancel] at h
  have hAdet : 0 < A.det := hA.det_pos
  have hBdet : 0 < B.det := hB.det_pos
  have hAunit : IsUnit A.det := hAdet.ne'.isUnit
  obtain ⟨D, hD⟩ : ∃ D, B = star D * D :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hD
  have hBD : B.det = D.det * D.det := by
    rw [hD, Matrix.det_mul, Matrix.det_conjTranspose, star_trivial]
  have hDunit : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det]
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    rw [h0, zero_mul] at hBD
    exact hBdet.ne' hBD
  have hM : (D * A⁻¹ * Dᴴ).PosDef :=
    hA.inv.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hDunit)
  have hkey := aux_logdet_le_trace _ hM
  have hdetM : (D * A⁻¹ * Dᴴ).det = B.det / A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, star_trivial,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hBD]
    field_simp
  have htrM : (D * A⁻¹ * Dᴴ).trace = (B * A⁻¹).trace := by
    rw [Matrix.trace_mul_comm, hD, Matrix.mul_assoc]
  have hlhs : ∑ i, ∑ j, A⁻¹ i j * (A - B) i j = ((A - B) * A⁻¹).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 := hA.inv.1.apply i j
    rw [star_trivial] at h1
    rw [h1, mul_comm]
  have htr : ((A - B) * A⁻¹).trace = n - (B * A⁻¹).trace := by
    rw [Matrix.sub_mul, Matrix.mul_nonsing_inv A hAunit, Matrix.trace_sub, Matrix.trace_one,
      Fintype.card_fin]
  rw [hlhs, htr, ← inv_div, Real.log_inv]
  rw [hdetM, htrM] at hkey
  linarith

end LogRegretOCO.ONS

open LogRegretOCO.ONS

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : (A - B).PosSemidef) (hB : B.PosDef) :
    ∑ i, ∑ j, A⁻¹ i j * (A - B) i j ≤ Real.log (A.det / B.det) :=
  aux_logdet_main A B hAB hB
