import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

namespace LogRegretOCO.ONS

open Matrix

theorem aux_gp_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (u v : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
  have hT : Aᵀ = A := by
    have h := hA.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]

theorem aux_gp_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (u v : Fin n → ℝ) (s : ℝ) :
    (u + s • v) ⬝ᵥ (A *ᵥ (u + s • v)) =
      u ⬝ᵥ (A *ᵥ u) + 2 * s * (u ⬝ᵥ (A *ᵥ v)) + s ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  have hs := aux_gp_symm A hA u v
  rw [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
    smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hs]
  simp only [smul_eq_mul]
  ring

theorem aux_gp_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
  have h := hA.dotProduct_mulVec_nonneg v
  simpa using h

end LogRegretOCO.ONS

open LogRegretOCO.ONS Matrix

theorem solution {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (hP : Convex ℝ P)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (y z : EuclideanSpace ℝ (Fin n)) (hz : IsGenProj P A y z) :
    ∀ a ∈ P, quadForm A (z - a) ≤ quadForm A (y - a) := by
  intro a ha
  obtain ⟨hzP, hmin⟩ := hz
  set u : Fin n → ℝ := WithLp.ofLp y - WithLp.ofLp z with hu
  set d : Fin n → ℝ := WithLp.ofLp a - WithLp.ofLp z with hd
  set b : ℝ := u ⬝ᵥ (A *ᵥ d) with hb
  set c : ℝ := d ⬝ᵥ (A *ᵥ d) with hc
  have hc0 : 0 ≤ c := aux_gp_nonneg A hA d
  -- first-order condition
  have hstep : ∀ s : ℝ, 0 < s → s ≤ 1 → 2 * s * b ≤ s ^ 2 * c := by
    intro s hs0 hs1
    have hw : z + s • (a - z) ∈ P := by
      have := hP.add_smul_sub_mem hzP ha ⟨hs0.le, hs1⟩
      exact this
    have h1 := hmin _ hw
    unfold quadForm at h1
    have e1 : WithLp.ofLp (y - z) = u := by simp [hu]
    have e2 : WithLp.ofLp (y - (z + s • (a - z))) = u + (-s) • d := by
      simp only [WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_smul, hu, hd]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, e2, aux_gp_expand A hA u d (-s)] at h1
    nlinarith
  have hb0 : b ≤ 0 := by
    by_contra hbneg
    have hbpos : 0 < b := lt_of_not_ge hbneg
    have hbc : 0 < b + c := by linarith
    set s : ℝ := b / (b + c) with hsdef
    have hs0 : 0 < s := div_pos hbpos hbc
    have hs1 : s ≤ 1 := by
      rw [hsdef, div_le_one hbc]; linarith
    have h := hstep s hs0 hs1
    -- 2 s b ≤ s^2 c  ⇒ 2 b ≤ s c ≤ c * s; and s * (b + c) = b
    have hsb : s * (b + c) = b := by
      rw [hsdef]; field_simp
    nlinarith
  unfold quadForm
  have e3 : WithLp.ofLp (y - a) = u + (-1 : ℝ) • d := by
    simp only [WithLp.ofLp_sub, hu, hd]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e4 : WithLp.ofLp (z - a) = 0 + (-1 : ℝ) • d := by
    simp only [WithLp.ofLp_sub, hd]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    ring
  rw [e3, e4, aux_gp_expand A hA u d (-1), aux_gp_expand A hA 0 d (-1)]
  have hu0 : 0 ≤ u ⬝ᵥ (A *ᵥ u) := aux_gp_nonneg A hA u
  simp only [zero_dotProduct, mulVec_zero, dotProduct_zero]
  nlinarith
