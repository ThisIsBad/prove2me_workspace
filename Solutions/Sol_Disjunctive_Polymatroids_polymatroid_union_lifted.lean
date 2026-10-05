import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic



namespace Disjunctive.Polymatroids

theorem lifted_cex_core : ¬ (∀ {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2),
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {w : Fin n → ℝ | (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
        ∃ x y : Fin n → ℝ, w = x + y ∧
          ∀ A B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
            1 ≤ ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) +
              ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B)}) := by
  intro h
  have hr : IsApp1SetFunction (fun _ : Finset (Fin 1) => (0:ℝ)) :=
    ⟨rfl, fun A _ => by positivity, fun _ _ _ => le_rfl⟩
  have H := h (fun _ : Finset (Fin 1) => (0:ℝ)) (fun _ => 0) hr hr
  have hw : (fun _ : Fin 1 => (1:ℝ)) ∈ convexHull ℝ
      (PolymatroidP (fun _ : Finset (Fin 1) => (0:ℝ)) ∪ PolymatroidP (fun _ => 0)) := by
    rw [H]
    refine ⟨fun i => ⟨by norm_num, le_rfl⟩, 0, fun _ => 1, by ext; simp, ?_⟩
    intro A B _ _
    have hB : SumOver (fun _ : Fin 1 => (1:ℝ)) B = B.card := by simp [SumOver]
    rw [hB]; simp [SumOver]
    rcases Finset.eq_empty_or_nonempty A with rfl | hA
    · simp_all
    · rw [div_self]; exact_mod_cast (Finset.card_pos.mpr hA).ne'
  have hsub : PolymatroidP (fun _ : Finset (Fin 1) => (0:ℝ)) ∪ PolymatroidP (fun _ => 0) ⊆
      {w : Fin 1 → ℝ | w 0 ≤ 0} := by
    intro w hw
    rcases hw with hw | hw <;>
    · have := hw.2 {0}
      simpa [SumOver] using this
  have hc : Convex ℝ {w : Fin 1 → ℝ | w 0 ≤ 0} := by
    have : {w : Fin 1 → ℝ | w 0 ≤ 0} = (fun w : Fin 1 → ℝ => w 0) ⁻¹' Set.Iic 0 := rfl
    rw [this]
    exact (convex_Iic 0).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have := convexHull_min hsub hc hw
  norm_num at this

end Disjunctive.Polymatroids

open Disjunctive.Polymatroids


theorem solution : ¬ (∀ {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2),
    convexHull ℝ (PolymatroidP r1 ∪ PolymatroidP r2) =
      {w : Fin n → ℝ | (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧
        ∃ x y : Fin n → ℝ, w = x + y ∧
          ∀ A B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
            1 ≤ ((A.card : ℝ) - SumOver x A) / ((A.card : ℝ) - r1 A) +
              ((B.card : ℝ) - SumOver y B) / ((B.card : ℝ) - r2 B)}) := lifted_cex_core
