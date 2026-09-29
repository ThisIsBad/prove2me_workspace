import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

lemma aux_inb_eq_zero (v : EuclideanSpace ℝ (Fin 0)) : v = 0 := Subsingleton.elim v 0

lemma aux_inb_zero_mem_clarkeJac (x : EuclideanSpace ℝ (Fin 0)) :
    (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) ∈
      clarkeJac (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : EuclideanSpace ℝ (Fin 0))) x := by
  apply subset_convexHull
  refine ⟨fun _ => x, tendsto_const_nhds, fun _ => differentiableAt_const _, ?_⟩
  have : (fun k : ℕ => fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : EuclideanSpace ℝ (Fin 0)))
      ((fun _ : ℕ => x) k)) = fun _ => 0 := by
    funext k; exact Subsingleton.elim _ _
  rw [this]
  exact tendsto_const_nhds

end NonsmoothNewton.Global

open NonsmoothNewton.Global
open Filter Topology

theorem solution : ¬ (∀ {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (hα : β * (γ + δ) < 1)
    (hr0 : 0 ≤ r) (hr : β * ‖F x0‖ ≤ r * (1 - β * (γ + δ)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hx0 : x 0 = x0) (hrun : IsNewtonRun F x V),
    ∀ k, x k ∈ Metric.closedBall x0 r ∧
      ‖x (k + 1) - x k‖ ≤ r * (β * (γ + δ)) ^ k * (1 - β * (γ + δ))) := by
  intro h
  have key := h (n := 0) (fun _ => 0) 0 1 1 (-1) 0
    (LipschitzWith.const (0 : EuclideanSpace ℝ (Fin 0))).locallyLipschitz
    (by
      intro y _
      refine ⟨⟨0, Set.univ, Filter.univ_mem, (LipschitzWith.const _).lipschitzOnWith⟩, ?_⟩
      intro hdir
      refine ⟨0, fun ε hε => ⟨1, one_pos, fun t h' _ _ _ W _ => ?_⟩⟩
      rw [aux_inb_eq_zero (W h' - 0), norm_zero]
      exact hε)
    (by
      intro y _ W _
      refine ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _, by simp⟩)
    (by
      intro a _ b _ W _
      rw [aux_inb_eq_zero (W (b - a) - _), aux_inb_eq_zero (b - a)]
      simp)
    (by
      intro a _ b _
      rw [aux_inb_eq_zero (_ - _ - _), aux_inb_eq_zero (b - a)]
      simp)
    (by norm_num) (by norm_num) (by simp)
    (fun _ => 0) (fun _ => 0) rfl
    (fun k => ⟨aux_inb_zero_mem_clarkeJac _, by simp⟩)
    1
  have h2 := key.2
  norm_num at h2
