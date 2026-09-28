import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

namespace LogRegretOCO.ONS

open scoped MatrixOrder Matrix

theorem aux_ep_logdet_le_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    Real.log M.det ≤ M.trace - n := by
  rw [hM.1.det_eq_prod_eigenvalues, hM.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [Real.log_prod (fun i _ => (hM.eigenvalues_pos i).ne')]
  have : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hM.eigenvalues_pos i)

theorem aux_ep_logdet {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
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
  have hkey := aux_ep_logdet_le_trace _ hM
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

theorem aux_ep_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    dotProduct x (M.mulVec x) = ∑ i, ∑ j, M i j * Matrix.vecMulVec x x i j := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_ep_psd {n : ℕ} (x : Fin n → ℝ) : (Matrix.vecMulVec x x).PosSemidef := by
  have := Matrix.posSemidef_vecMulVec_self_star x
  simpa using this

theorem aux_ep_telescope {n : ℕ} (V : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Fin n → ℝ)
    (h0 : (V 0).PosDef) (hs : ∀ s, V (s + 1) = V s + Matrix.vecMulVec (x (s + 1)) (x (s + 1)))
    (T : ℕ) :
    (V T).PosDef ∧ ∑ t ∈ Finset.Icc 1 T, dotProduct (x t) ((V t)⁻¹.mulVec (x t))
      ≤ Real.log (V T).det - Real.log (V 0).det := by
  induction T with
  | zero => exact ⟨h0, by simp⟩
  | succ s ih =>
    obtain ⟨hVs, hsum⟩ := ih
    have hpsd := aux_ep_psd (x (s + 1))
    have hVs1 : (V (s + 1)).PosDef := by rw [hs]; exact hVs.add_posSemidef hpsd
    refine ⟨hVs1, ?_⟩
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hdiff : V (s + 1) - V s = Matrix.vecMulVec (x (s + 1)) (x (s + 1)) := by
      rw [hs]; abel
    have key := aux_ep_logdet (V (s + 1)) (V s) (by rw [hdiff]; exact hpsd) hVs
    rw [hdiff, ← aux_ep_quad, Real.log_div hVs1.det_pos.ne' hVs.det_pos.ne'] at key
    linarith

theorem aux_ep_main {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ) (T : ℕ)
    (hε : 0 < ε) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r)
    (V : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hV : ∀ t, V t = ∑ τ ∈ Finset.Icc 1 t, Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ))
        + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    ∑ t ∈ Finset.Icc 1 T, dotProduct (WithLp.ofLp (u t)) (Matrix.mulVec (V t)⁻¹ (WithLp.ofLp (u t)))
      ≤ n * Real.log (r ^ 2 * T / ε + 1) := by
  have hV0 : V 0 = ε • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hV]; simp
  have h0 : (V 0).PosDef := by
    rw [hV0]; exact Matrix.PosDef.one.smul hε
  have hs : ∀ s, V (s + 1) = V s + Matrix.vecMulVec (WithLp.ofLp (u (s + 1)))
      (WithLp.ofLp (u (s + 1))) := by
    intro s
    rw [hV, hV, Finset.sum_Icc_succ_top (by omega)]
    abel
  obtain ⟨hVT, htel⟩ := aux_ep_telescope V (fun t => WithLp.ofLp (u t)) h0 hs T
  have hdet0 : Real.log (V 0).det = n * Real.log ε := by
    rw [hV0, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, Real.log_pow]
  have hT0 : (0 : ℝ) ≤ r ^ 2 * T := by positivity
  have hK : 0 < r ^ 2 * T + ε := by linarith
  -- trace bound
  have htr : (V T).trace ≤ n * (r ^ 2 * T + ε) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [Matrix.trace]
    · have hnorm : ∀ τ, dotProduct (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ)) = ‖u τ‖ ^ 2 := by
        intro τ
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [dotProduct, sq]
      have hsumle : ∑ τ ∈ Finset.Icc 1 T, ‖u τ‖ ^ 2 ≤ ∑ τ ∈ Finset.Icc 1 T, r ^ 2 :=
        Finset.sum_le_sum fun τ hτ => pow_le_pow_left₀ (norm_nonneg _) (hu τ hτ) 2
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsumle
      have hcast : ((T + 1 - 1 : ℕ) : ℝ) = T := by simp
      rw [hcast] at hsumle
      rw [hV, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one,
        Fintype.card_fin, smul_eq_mul]
      simp only [Matrix.trace_vecMulVec, hnorm]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  -- log det bound
  have hlogdet : Real.log (V T).det ≤ n * Real.log (r ^ 2 * T + ε) := by
    set c : ℝ := (r ^ 2 * T + ε)⁻¹ with hc
    have hcpos : 0 < c := inv_pos.mpr hK
    have hM : (c • V T).PosDef := hVT.smul hcpos
    have key := aux_ep_logdet_le_trace _ hM
    rw [Matrix.det_smul, Fintype.card_fin, Real.log_mul (pow_ne_zero _ hcpos.ne') hVT.det_pos.ne',
      Real.log_pow, Matrix.trace_smul, smul_eq_mul, hc, Real.log_inv] at key
    have hct : (r ^ 2 * T + ε)⁻¹ * (V T).trace ≤ n := by
      rw [inv_mul_le_iff₀ hK]; linarith
    linarith
  have hlog : Real.log (r ^ 2 * T / ε + 1) = Real.log (r ^ 2 * T + ε) - Real.log ε := by
    rw [← Real.log_div hK.ne' hε.ne']
    congr 1
    field_simp
  rw [hlog, mul_sub]
  linarith

end LogRegretOCO.ONS


open LogRegretOCO.ONS

theorem solution {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (T : ℕ) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r) :
    ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε u t)⁻¹ (u t) ≤
      n * Real.log (r ^ 2 * T / ε + 1) :=
  aux_ep_main u r ε T hε hu (regGram ε u) (fun _ => rfl)
