import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau

namespace Disjunctive.CutCorrespondence

namespace Cex85

def At : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
noncomputable def bt : Fin 1 → ℝ := fun _ => 1 / 2

lemma feas_unique (w : (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ × (Fin 1 → ℝ) × ℝ × ℝ)
    (hw : w ∈ CGLPKFeasibleSet At bt 0) (hv : w.2.2.2.1 0 = 0) :
    w = (fun _ => 1 / 4, fun _ => 1 / 2, 1 / 4, fun _ => 0, 1 / 4, 1 / 4) := by
  obtain ⟨α, u, u0, v, v0, β⟩ := w
  simp only [CGLPKFeasibleSet, IsCGLPKFeasible, Set.mem_setOf_eq] at hw
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -⟩ := hw
  have e1 := h1 0
  have e2 := h2 0
  simp only [Fin.sum_univ_one, At, bt, if_true, mul_one] at e1 e2 h3 h4 h5 hv
  rw [hv] at e2 h4 h5
  have hv0 : v0 = 1 / 4 := by linarith
  simp only [Prod.mk.injEq]
  refine ⟨funext fun i => ?_, funext fun i => ?_, ?_, funext fun i => ?_, ?_, ?_⟩
  · rw [Subsingleton.elim i 0]; linarith
  · rw [Subsingleton.elim i 0]; linarith
  · linarith
  · rw [Subsingleton.elim i 0]; exact hv
  · linarith
  · linarith

lemma basic : IsBasicCGLPKSolution At bt 0 (fun _ => 1 / 4) (fun _ => 1 / 2) (1 / 4) (fun _ => 0)
    (1 / 4) (1 / 4) := by
  have hmem : ((fun _ => 1 / 4 : Fin 1 → ℝ), (fun _ => 1 / 2 : Fin 1 → ℝ), (1 / 4 : ℝ),
      (fun _ => 0 : Fin 1 → ℝ), (1 / 4 : ℝ), (1 / 4 : ℝ)) ∈ CGLPKFeasibleSet At bt 0 := by
    simp only [CGLPKFeasibleSet, IsCGLPKFeasible, Set.mem_setOf_eq, Fin.sum_univ_one, At, bt]
    refine ⟨fun i => ?_, fun i => ?_, by norm_num, by norm_num, by norm_num,
      fun _ => by norm_num, fun _ => by norm_num, by norm_num, by norm_num⟩
    · rw [Subsingleton.elim i 0]; norm_num
    · rw [Subsingleton.elim i 0]; norm_num
  refine mem_extremePoints.mpr ⟨hmem, fun x1 hx1 x2 hx2 hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hseg
  have hv1 : 0 ≤ x1.2.2.2.1 0 := hx1.2.2.2.2.2.2.1 0
  have hv2 : 0 ≤ x2.2.2.2.1 0 := hx2.2.2.2.2.2.2.1 0
  have hsum : a * x1.2.2.2.1 0 + b * x2.2.2.2.1 0 = 0 := by
    have := congrArg (fun w => w.2.2.2.1 0) hx
    simpa using this
  have z1 : x1.2.2.2.1 0 = 0 := by nlinarith [mul_nonneg ha.le hv1, mul_nonneg hb.le hv2]
  have z2 : x2.2.2.2.1 0 = 0 := by nlinarith [mul_nonneg ha.le hv1, mul_nonneg hb.le hv2]
  exact ⟨feas_unique x1 hx1 z1, feas_unique x2 hx2 z2⟩

lemma ahat_eq : Ahat At (id : Fin 1 → Fin 1) = 1 := by
  ext i j; rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp [Ahat, At]

theorem cex85 : ¬ (∀ {n : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (Nprime : Finset (Fin n))
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_inj : Function.Injective ι) (hι_image : Finset.image ι Finset.univ = M1 ∪ M2)
    (hnonsing : IsUnit (Ahat Atil ι).det),
    {x | β ≤ dotProduct (Gamma Atil u u0 v v0 k Nprime α) x} =
      StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) := by
  intro h
  have := h At bt 0 (fun _ => 1 / 4) (fun _ => 1 / 2) (1 / 4) (fun _ => 0) (1 / 4) (1 / 4)
    Finset.univ Finset.univ id {0} basic (by norm_num) (by norm_num) (by simp) (by simp)
    Function.injective_id (by simp) (by rw [ahat_eq]; simp)
  have hx : (fun _ => 1 : Fin 1 → ℝ) ∈ {x | (1 / 4 : ℝ) ≤ dotProduct
      (Gamma At (fun _ => 1 / 2) (1 / 4) (fun _ => 0) (1 / 4) 0 {0} (fun _ => 1 / 4)) x} := by
    simp only [Set.mem_setOf_eq, dotProduct, Fin.sum_univ_one, mul_one]
    have hm : MBar At (fun _ => 1 / 2) (1 / 4) (fun _ => 0) (1 / 4) 0 0 = ((-2 : ℤ) : ℝ) := by
      simp only [MBar, Alpha1, Alpha2, Fin.sum_univ_one, At, if_true]; norm_num
    simp only [Gamma, Finset.mem_singleton, if_true, hm, Int.ceil_intCast, Int.floor_intCast,
      Alpha1, Alpha2, Fin.sum_univ_two, Fin.sum_univ_one, At]
    norm_num
  rw [this] at hx
  simp only [StrengthenedSimpleDisjCutSet, Set.mem_setOf_eq, Fin.sum_univ_one, PiBar,
    Finset.mem_singleton, if_true, FracAbar, Abar, Pi0, Abar0, ahat_eq, inv_one,
    Matrix.one_mulVec, Bhat, bt, id] at hx
  norm_num at hx

end Cex85

end Disjunctive.CutCorrespondence

open Disjunctive.CutCorrespondence

theorem solution : ¬ (∀ {n : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (Nprime : Finset (Fin n))
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_inj : Function.Injective ι) (hι_image : Finset.image ι Finset.univ = M1 ∪ M2)
    (hnonsing : IsUnit (Ahat Atil ι).det),
    {x | β ≤ dotProduct (Gamma Atil u u0 v v0 k Nprime α) x} =
      StrengthenedSimpleDisjCutSet Atil btil ι k Nprime) := by
  exact Disjunctive.CutCorrespondence.Cex85.cex85
