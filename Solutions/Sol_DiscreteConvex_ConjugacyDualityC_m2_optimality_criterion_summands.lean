import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MExchangeAxiom

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.ConjugacyDualityC

namespace M2Cex

/-- `y ↦ c * y 0` on the hyperplane `y 0 + y 1 = 0`. -/
noncomputable def F (c : ℝ) (y : Fin 2 → ℤ) : WithTop ℝ :=
  if y 0 + y 1 = 0 then ((c * (y 0 : ℝ) : ℝ) : WithTop ℝ) else ⊤

theorem F_of (c : ℝ) (y : Fin 2 → ℤ) (h : y 0 + y 1 = 0) : F c y = ((c * (y 0 : ℝ) : ℝ) : WithTop ℝ) := by
  simp [F, h]

theorem F_dom (c : ℝ) (y : Fin 2 → ℤ) (h : y ∈ DomZ (F c)) : y 0 + y 1 = 0 := by
  by_contra hc
  simp [DomZ, F, hc] at h

theorem F_exc (c : ℝ) : MExchangeAxiom (F c) := by
  intro x hx y hy u hu
  have hx' := F_dom c x hx
  have hy' := F_dom c y hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  fin_cases u
  · refine ⟨1, ?_, ?_⟩
    · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
      simp at hu; omega
    · rw [F_of c x hx', F_of c y hy', F_of, F_of]
      · apply le_of_eq; rw [← WithTop.coe_add, ← WithTop.coe_add]; congr 1
        simp [IndicatorVec]; ring
      · simp [IndicatorVec]; omega
      · simp [IndicatorVec]; omega
  · refine ⟨0, ?_, ?_⟩
    · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
      simp at hu; omega
    · rw [F_of c x hx', F_of c y hy', F_of, F_of]
      · apply le_of_eq; rw [← WithTop.coe_add, ← WithTop.coe_add]; congr 1
        simp [IndicatorVec]; ring
      · simp [IndicatorVec]; omega
      · simp [IndicatorVec]; omega

end M2Cex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MExchangeAxiom f1)
    (hf2 : MExchangeAxiom f2) (x : V → ℤ) (hx : x ∈ DomZ f1 ∩ DomZ f2),
    (∀ y : V → ℤ, f1 x + f2 x ≤ f1 y + f2 y) ↔
      (∀ k : ℕ, ∀ u v : Fin (k + 1) → V, (∀ i j, u i ≠ v j) →
        (∑ i : Fin (k + 1),
            (f1 (fun w => x w - IndicatorVec {u i} w + IndicatorVec {v i} w) - f1 x)) +
          (∑ i : Fin (k + 1),
            (f2 (fun w => x w + IndicatorVec {u (i + 1)} w - IndicatorVec {v i} w) - f2 x)) ≥
          0)) := by
  intro h
  have h0 : (0 : Fin 2 → ℤ) ∈ DomZ (M2Cex.F 1) ∩ DomZ (M2Cex.F (-1)) := by
    constructor <;> simp [DomZ, M2Cex.F]
  have key := (h (M2Cex.F 1) (M2Cex.F (-1)) (M2Cex.F_exc 1) (M2Cex.F_exc (-1)) 0 h0).1 ?_ 0
    (fun _ => 0) (fun _ => 1) (by decide)
  · rw [Fin.sum_univ_one, Fin.sum_univ_one] at key
    rw [M2Cex.F_of, M2Cex.F_of, M2Cex.F_of, M2Cex.F_of] at key
    · rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_add, ge_iff_le,
        ← WithTop.coe_zero, WithTop.coe_le_coe] at key
      simp [IndicatorVec] at key
      norm_num at key
    all_goals simp [IndicatorVec]
  · intro y
    rw [M2Cex.F_of _ _ (by simp), M2Cex.F_of _ _ (by simp)]
    by_cases hy : y 0 + y 1 = 0
    · rw [M2Cex.F_of _ _ hy, M2Cex.F_of _ _ hy, ← WithTop.coe_add, ← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr (by simp)
    · simp [M2Cex.F, hy]
